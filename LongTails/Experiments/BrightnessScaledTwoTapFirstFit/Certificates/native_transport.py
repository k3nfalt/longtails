import json
import math
import sys
import time
from pathlib import Path

import numpy as np
import torch
from native_data import read_native

input_path, mode, work = sys.argv[1:4]
rate, stop = sys.argv[4:]
root_power = {"sqrt8": 3, "sqrt2over8": -5}.get(rate)
eta = 2.0 ** (root_power / 2) if root_power is not None else int(rate)
T = int(stop)
p = Path(work)
out = p / "audit.json"
hist = {}
r = 1e-13
K, v, c0 = read_native(input_path)
v0n = (v * 2**30).astype(np.int64)
c = (c0 * 2**24).astype(np.int64)
Ks = np.roll(K, 1, axis=1)
raw = c[0] * K + c[1] * Ks
Fs = np.stack([K @ v0n, Ks @ v0n], 1)
assert np.max(abs(Fs)) < 2**53 and np.max(abs(raw)) < 2**53
assert mode in ("raw", "tangent")
exactrounded = (
    np.concatenate((raw / (255 * 2.0**24), Fs / (255 * 2.0**30)), 1)
    if mode == "tangent"
    else K / 255.0
)
X = torch.as_tensor(exactrounded, device="cuda")
n, d = X.shape
identity = torch.eye(d, device="cuda", dtype=X.dtype)


def up(x):
    return x * (1 + 1e-7) + 1e-260


def nf(x):
    return up(float(torch.linalg.vector_norm(x)))


u = 2**-53
gn = n * u / (1 - n * u)
gd = d * u / (1 - d * u)
Hround = 1e-8
R = math.sqrt(d)
assert float(X.norm(dim=1).max()) * (1 + 1e-5) < R and (3 * gn + 100 * u) * d < Hround
localbits = 25.0


def op(M):
    F = nf(M)
    G = M.T @ M
    E = up(gd * F * F)
    log = 0.0
    k = 1
    for i in range(4):
        scale = up(float(G.abs().sum(1).max()))
        bound = up(math.exp((log + math.log(up(scale + R * E))) / (2 * k)))
        if i == 3:
            return min(F, bound)
        log = 2 * (log + math.log(scale))
        Y = G / scale
        yf = nf(Y)
        e = up(E / scale + 4 * u * yf)
        E = up(2 * yf * e + e * e + gd * yf * yf)
        G = Y @ Y
        k *= 2


def lgadd(a, b):
    if a < b:
        a, b = b, a
    return a + math.log2(1.0 + 2.0 ** (b - a)) + 1e-9


Q = np.load(p / "Q.npy", mmap_mode="r")
before = 0
start = 0
seen = -1
block = []
pm = identity.clone()
pe = 0.0
within = 0.0
lgC = -float("inf")
lgmax = -float("inf")
tau = time.monotonic()
Fmax = 0.0
Amax = 0.0
tap = 0
for t in range(T):
    if t >= seen:
        while True:
            try:
                histp = json.loads((p / "progress.json").read_text())
                seen = int(list(histp)[-1])
            except (ValueError, FileNotFoundError):
                seen = -1
            if seen > t:
                break
            time.sleep(2)
    q = torch.from_numpy(np.asarray(Q[t]).copy()).cuda()
    J = X * ((q * (1 - q) / n).sqrt())[:, None]
    H = J.T @ J
    A = identity - eta * H
    hf = nf(H)
    af = nf(A)
    pf = nf(pm)
    # X rational /255, full precision sigmoid given in nearest-rounded binary64, and secant over any spatial error r.
    da = up(
        eta * (Hround + (hf + Hround) * R * r * 1.00001)
        + 16 * u * (math.sqrt(d) + eta * hf)
        + 1e-13
    )
    M = up(max(1.0, eta * hf - 1) + da + eta * Hround)
    within += math.log2(M) + 1e-9
    Fmax = max(Fmax, hf)
    Amax = max(Amax, da)
    pe = up(M * pe + (da + gd * af) * pf)
    pm = A @ pm
    tap += 1
    # Allows any r-bounded secants, including interpolation between the true and fixed-point reference.
    if tap == 4 or t + 1 == T:
        block.append((pm, pe, op(pm)))
        pm = identity.clone()
        pe = 0.0
        tap = 0
    if len(block) == 16 or t + 1 == T:
        h = t + 1 - start
        prec = min(
            v["P"]
            for k, v in histp.items()
            if int(k) >= max(start // 256 * 256, 0) and int(k) <= min(t + 1, seen)
        )
        eps_lg = -prec + localbits
        prev = lgC
        lgmax = max(lgmax, within + lgadd(prev, math.log2(h) + eps_lg) + 1e-8)
        while len(block) > 1:
            layer = []
            for j in range(0, len(block) - 1, 2):
                Rm, e0, n0 = block[j]
                Lm, e1, n1 = block[j + 1]
                pc = Lm @ Rm
                EE = up(e0 * n1 + e1 * (n0 + e0) + gd * nf(Rm) * nf(Lm))
                layer.append((pc, EE, op(pc)))
            if len(block) % 2:
                layer.append(block[-1])
            block = layer
        _, e, s = block[0]
        bound = up(e + s)
        lgC = lgadd(prev + math.log2(bound), within + math.log2(h) + eps_lg)
        lgmax = max(lgmax, lgC)
        assert lgmax < math.log2(r) - 1e-8, (t, lgmax, prec)
        hist[t + 1] = {
            "rounding_precision": prec,
            "end_param_error_log2": lgC,
            "max_param_error_log2": lgmax,
            "secant_tube": r,
            "max_hessian_F": Fmax,
            "max_secant_error": Amax,
            "op": bound,
            "within_log2": within,
            "elapsed": time.monotonic() - tau,
        }
        tmp = p / "audit-swap.json"
        tmp.write_text(json.dumps(hist, indent=1))
        tmp.replace(out)
        if t + 1 == T or (t + 1) % 1024 == 0:
            print(t + 1, lgmax, lgC, prec, time.monotonic() - tau, flush=True)
        block = []
        start = t + 1
        within = 0.0
final = json.loads((p / "progress.json").read_text())[str(T)]
assert final["max_abs_margin"] < 1e6 and final["max_min_margin"] + R * r + 2**-32 < 0
print("Certified strict nonfit through", T, "inclusive")
