import sys
from fractions import Fraction

import numpy as np
import torch as t
from scipy.optimize import brentq

ds = sys.argv[1]
cap = int(sys.argv[2])
mode = sys.argv[3] if len(sys.argv) > 3 else "native"
z = np.load(ds)
X = t.tensor(z["levels"][z["codes"]], dtype=t.float64, device="cuda")
n, d = X.shape
dc = X.mean(1) * np.sqrt(2 * d)
A = (X - X.roll(1, 1)) / np.sqrt(2)
C = (X + X.roll(1, 1)) / np.sqrt(2) - dc[:, None] / np.sqrt(d)
a = float(dc.clamp_min(0).mean())
b = float((-dc).clamp_min(0).mean())

k0 = 0.7 / max(a, b)
ratio = Fraction(np.arctanh(k0 * a) / np.arctanh(k0 * b)).limit_denominator(23)


def fn(k):
    return np.arctanh(k * a) / np.arctanh(k * b) - float(ratio)


kap = (
    brentq(fn, 1e-10, (1 - 1e-10) / max(a, b))
    if fn(1e-10) * fn((1 - 1e-10) / max(a, b)) < 0
    else k0
)
R = t.tensor(
    [1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0, 256.0, 1024.0, 16384.0, 1048576.0],
    device="cuda",
    dtype=X.dtype,
)
P0 = sum(z["c0"]) / np.sqrt(2)
Q0 = (z["c0"][0] - z["c0"][1]) / np.sqrt(2)
if mode == "identity":
    P0 = Q0 = 1 / np.sqrt(2)
v0 = t.as_tensor(z["v0"], device="cuda", dtype=X.dtype)
P = t.full_like(R, P0)
Q = t.full_like(R, Q0)
T = v0.sum() / np.sqrt(d) / R.square()
v = (v0 - v0.mean())[:, None].repeat(1, len(R))
# Select the asymptotic contrast-readout scale using the covariance before training.
if mode == "calibrated":
    lam = float(t.linalg.eigvalsh(A.T @ A / n)[-1]) / 4
    E = 1 / (lam * Q0**2 * kap)
    scale = (1 + E * (R - 1)) / R
    print("contrast covariance /4", lam, "squared gauge /R limit", E, flush=True)
else:
    scale = t.ones_like(R)
N = 128
hit = t.zeros((N, len(R)), device="cuda", dtype=t.bool)
best = t.full_like(R, -1, dtype=t.long)


def block():
    for j in range(N):
        av = A @ v
        cv = C @ v
        m = R.square() * scale * P * T * dc[:, None] + Q * av + P * cv
        g = t.sigmoid(-m)
        hit[j] = (m > 0).all(0)
        f = dc @ g / n
        e = (cv * g).mean(0)
        a = (av * g).mean(0)
        dv = (A.T @ g) * (kap * scale * Q / n) + (C.T @ g) * (kap * scale * P / n)
        dp = kap * f * T + (kap * e) / (R.square() * scale)
        dt = kap * f * P
        P.add_(dp)
        T.add_(dt)
        Q.add_(kap * a / (R.square() * scale))
        v.add_(dv)


orig = [w.clone() for w in (P, T, Q, v)]
T.div_(scale)
orig = [w.clone() for w in (P, T, Q, v)]
stream = t.cuda.Stream()
stream.wait_stream(t.cuda.current_stream())
with t.cuda.stream(stream):
    block()
stream.synchronize()
gr = t.cuda.CUDAGraph()
with t.cuda.graph(gr):
    block()
for w, src in zip((P, T, Q, v), orig):
    w.copy_(src)
ks = t.arange(N, device="cuda")[:, None]
print("kap", kap, "rotation", ratio, "scales", R.tolist(), flush=True)
for j in range(0, cap, N):
    gr.replay()
    h = t.where(hit, ks + j, cap + N).amin(0)
    best = t.where((best < 0) & (h < cap), h, best)
    if j // N + 1 in (1, 4, 16, 64, 256, 1024, 4096, 16384, 65536) or j + N >= cap:
        print(
            j + N,
            best.tolist(),
            "p",
            P.tolist(),
            "Q",
            Q.tolist(),
            "vnorm",
            v.norm(dim=0).tolist(),
            flush=True,
        )
    if best.min() >= 0:
        break
np.savez(sys.argv[4], h=kap, R=R.cpu().numpy(), hit=best.cpu().numpy(), cap=cap)
