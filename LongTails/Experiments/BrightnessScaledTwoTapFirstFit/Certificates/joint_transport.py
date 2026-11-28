import json
import math
import sys
import time
from decimal import Decimal as D
from decimal import getcontext
from pathlib import Path

import numpy as np
import torch
from native_data import read_native

torch.set_default_dtype(torch.float64)
root_rate = "sqrt2over8" in sys.argv[3:]
Pbit, T = (2048, 21000) if root_rate else (1024, 23444)
ref = Path(sys.argv[2])
targets = [x for x in sys.argv[3:] if x != "sqrt2over8"]
target = Path(targets[0]) if targets else ref
target.mkdir(exist_ok=True, parents=True)
H, _, _ = read_native(sys.argv[1])
Z = torch.tensor(H, dtype=torch.float64, device="cuda")
X = Z / 255
XS = X.roll(1, 1).contiguous()
n, d = X.shape
p = d + 2
torch.backends.cuda.matmul.allow_tf32 = False
arr = {
    k: np.load(ref / (k + ".npy"), mmap_mode="r") for k in ["V", "C", "Q", "YV", "G"]
}
ut = 2**-53
gn = n * ut / (1 - n * ut)
gd = p * ut / (1 - p * ut)


def inflate(s):
    return s * (1 + 1e-7) + 1e-290


def norm(a):
    return inflate(float(torch.linalg.vector_norm(a)))


eta = math.sqrt(2) / 8 if root_rate else 0.125
Id = torch.eye(p, device="cuda")
J = X.new_empty(n, p)
W = Id.clone()
Pr = Id.clone()
prevW = norm(W)
prevP = norm(Pr)
t0 = time.monotonic()
out = {}
start = 0
Cstart = 0.0
Cmax = 0.0
pe2 = 0.0
eps = 0.0
localK = 1.0
localPP = 1.0
Amax = 0.0
normmax = 0.0
minabs_m = float("inf")
prehitworst = -math.inf
first = None
firstpositive = None
nsets = 0
seen = -1
for t in range(T):
    if t > seen:
        while True:
            try:
                seen = int(list(json.loads((ref / "progress.json").read_text()))[-1])
            except (ValueError, FileNotFoundError):
                seen = -1
            if seen >= t:
                break
            time.sleep(2)
    v, c, q, yv, g = [
        torch.from_numpy(np.asarray(arr[k][t]).copy()).cuda()
        for k in ["V", "C", "Q", "YV", "G"]
    ]
    meanvecNorm = inflate(math.hypot(norm(v), norm(c)))
    normmax = max(normmax, meanvecNorm)
    m = yv @ c
    worst = float(m.min())
    minabs_m = min(minabs_m, abs(worst))
    if first is None:
        if worst > 1e-10:
            first = t
            firstpositive = worst
        else:
            prehitworst = max(prehitworst, worst)
    Y = c[0] * X + c[1] * XS
    rawF = inflate(math.hypot(norm(Y), norm(yv)) / math.sqrt(n))
    w = q * (1 - q)
    wt = (w / n).sqrt()
    J[:, :d] = Y * wt[:, None]
    J[:, d:] = yv * wt[:, None]
    jF2 = inflate(norm(J) ** 2)
    H = J.T @ J
    sg = g.roll(1)
    H[:d, d] -= g
    H[d, :d] -= g
    H[:d, d + 1] -= sg
    H[d + 1, :d] -= sg
    A = Id - eta * H
    aF = norm(A)
    # Operator Jacobian error relative to exact sigmoid at exact fixed-point state. Precomputed Yv and q have correctly rounded FP64 enclosures up to 2^(-Pbit-50).
    jerr = inflate(16 * ut * math.sqrt(2 * d) * meanvecNorm + 1e-290)
    gnerr = (
        (gn + 16 * ut) * jF2
        + 8 * ut * rawF**2
        + (2 * rawF * jerr + jerr * jerr)
        + 5 * ut * math.sqrt(d)
    )
    da = inflate(
        eta * gnerr + 64 * ut * (math.sqrt(p) + eta * (jF2 + 4 * math.sqrt(d))) + 1e-14
    )
    Amax = max(Amax, da)
    # Verified additive error for W_new relative to A_exact W A_exact^T+I, including symmetrization.
    werr = inflate(
        ((3 * gd + 16 * ut) * aF * aF + 2 * da * aF + da**2) * prevW
        + 16 * ut * math.sqrt(p)
        + 1e-13
    )
    eps = max(eps, werr)
    assert eps < 0.95, (t, eps, prevW, da, aF)
    perr_i = inflate((gd * aF + da) * prevP + 1e-14)
    pe2 = inflate(pe2 + perr_i**2)
    Pr = A @ Pr
    W = A @ (W @ A.T) + Id
    W = (W + W.T) * 0.5
    prevW = norm(W)
    prevP = norm(Pr)
    K = inflate(math.sqrt(prevW / (1 - eps)))
    perr = inflate(K * math.sqrt(pe2))
    localK = max(localK, K)
    localPP = max(localPP, prevP + perr)
    Cmax = max(Cmax, inflate((prevP + perr) * Cstart + K * math.sqrt(t + 1 - start)))
    if (
        t + 1 - start >= (8 if t < 128 else 256)
        or prevW > 1e6
        or eps > 0.35
        or t + 1 == T
    ):
        gram = Pr.T @ Pr
        est = float(torch.linalg.eigvalsh(gram)[-1])
        U = inflate((est + 1e-7) * (1 + 1e-6))
        L, flag = torch.linalg.cholesky_ex(U * Id - gram)
        status = int(flag)
        if status:
            op = prevP
        else:
            residual = norm(U * Id - gram - L @ L.T)
            lf2 = inflate(norm(L) ** 2)
            ef = inflate(
                residual
                + (gd + 16 * ut) * (prevP**2 + lf2)
                + 16 * ut * math.sqrt(p) * U
                + 1e-13
            )
            op = inflate(math.sqrt(U + ef))
        M = inflate(op + perr)
        cb = inflate(K * math.sqrt(t + 1 - start))
        eend = inflate(M * Cstart + cb)
        Cmax = max(Cmax, eend)
        out[t + 1] = {
            "first": start,
            "last": t + 1,
            "observed_min_margin": worst,
            "gramian_epsilon": eps,
            "op_norm_upper": M,
            "approximate_op_upper": op,
            "operator_error": perr,
            "max_A_error": Amax,
            "max_local_amplification": localK,
            "max_prefix_fro": localPP,
            "local_endpoint_unit_defect": cb,
            "max_param_norm": normmax,
            "global_unit_defect": Cmax,
            "first_positive_reference": first,
            "prehit_max_worst_margin": prehitworst,
            "first_positive_min_margin": firstpositive,
            "min_abs_worst_so_far": minabs_m,
            "elapsed": time.monotonic() - t0,
        }
        nsets += 1
        (target / "bounds.json").write_text(json.dumps(out, indent=1))
        print(
            t + 1,
            round(math.log10(max(1, Cmax)), 3),
            round(eps, 5),
            round(time.monotonic() - t0, 2),
            flush=True,
        ) if nsets % 8 == 0 else None
        start = t + 1
        Cstart = eend
        W = Id.clone()
        Pr = Id.clone()
        prevW = norm(W)
        prevP = norm(Pr)
        pe2 = 0.0
        eps = 0.0
        localK = 1.0
        localPP = 1.0
        Amax = 0.0

getcontext().prec = 55
p = target
bounds = json.loads((p / "bounds.json").read_text())
b = bounds[str(T)]
C = D(str(b["global_unit_defect"])) * D("1.00001")
norm = D(str(b["max_param_norm"])) * D("1.00001")
Q = D(2) ** (-Pbit)
eps = ((D(32) + D(16) * norm) if root_rate else (D(28) + D("2.1") * norm)) * Q
Ddim = D(6144)
J = Ddim.sqrt() * (1 + norm)
L = (J**3 + 3 * Ddim * (1 + norm)) / 4
z = 2 * C * eps * (1 + D("1e-6"))
gain = (C * (eps + (D(1) / 10 if root_rate else D(1) / 16) * L * z * z)) / z
dmargin = J * z + D("1e-10")
out = {
    "T": T + 0,
    "P": Pbit,
    "nblocks": sum(int(k) <= T for k in bounds),
    "first": b["first_positive_reference"],
    "first_positive_min": b["first_positive_min_margin"],
    "max_preceding_worst": b["prehit_max_worst_margin"],
    "global_defect_gain": str(C),
    "local_defect": str(eps),
    "hessian_lipschitz": str(L),
    "bootstrap_fraction": str(gain),
    "parameter_error": str(z),
    "margin_error_upper": "1.000001e-10",
    "passes": bool(
        gain < D(1)
        and z < D(1)
        and dmargin < D("1.000001e-10")
        and D(str(b["first_positive_min_margin"])) > dmargin
        and D(str(b["prehit_max_worst_margin"])) < -dmargin
    ),
    "max_gramian_residual": max(
        v["gramian_epsilon"] for k, v in bounds.items() if int(k) <= T
    ),
}
assert out["passes"]
(p / "first-hit.json").write_text(json.dumps(out, indent=2))
print(out)
