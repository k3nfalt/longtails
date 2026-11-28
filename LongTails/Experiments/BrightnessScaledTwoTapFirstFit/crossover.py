import math
import sys

import numpy as np
import torch as t

ds, mode = sys.argv[1:3]
cap = int(sys.argv[3])
z = np.load(ds)
X = t.tensor(z["levels"][z["codes"]], dtype=t.float64, device="cuda")
n, d = X.shape
dc = X.mean(1) * math.sqrt(2 * d)
A = (X - X.roll(1, 1)) / math.sqrt(2)
C = (X + X.roll(1, 1)) / math.sqrt(2) - dc[:, None] / math.sqrt(d)
v = t.tensor(z["v0"], dtype=X.dtype, device="cuda")
P0 = sum(z["c0"]) / math.sqrt(2)
Q0 = (z["c0"][0] - z["c0"][1]) / math.sqrt(2)
R0, ks = np.meshgrid(
    [1.0, 2.0, 8.0, 64.0, 1024.0, 1048576.0],
    [0.01434237, 0.057369485, 0.125, 0.1767766953, 0.3535533906, 1.0, 2.8284271247],
    indexing="ij",
)
R = t.as_tensor(R0.flatten(), device="cuda")
h = t.as_tensor(ks.flatten(), device="cuda")
lam = float(t.linalg.eigvalsh(A.T @ A / n)[-1]) / 4
scale = (1 + (R - 1) / (0.057369485 * Q0**2 * lam)) / R
B = R.square() * scale
T0 = v.sum() / math.sqrt(d) / B
ac = (A @ (v - v.mean()))[:, None]
cc = (C @ (v - v.mean()))[:, None]
m0 = Q0 * ac + P0 * cc + dc[:, None] * P0 * (v.sum() / math.sqrt(d))
dp = t.zeros_like(h)
dt = dp.clone()
dq = dp.clone()
dv = t.zeros((d, h.numel()), dtype=h.dtype, device="cuda")
e = int("b" in mode)
c = int("c" in mode)
a = int("a" in mode)
N = 32
hit = t.empty((N, len(h)), dtype=t.bool, device="cuda")


def block():
    for j in range(N):
        av = A @ dv
        cv = C @ dv
        Q = Q0 + a * dq
        P = P0 + c * dp
        m = (
            m0
            + av * Q
            + cv * P
            + ac * dq
            + cc * dp
            + dc[:, None] * B * (P0 * dt + T0 * dp + e * dp * dt)
        )
        hit[j] = t.isfinite(m).all(0) & (m > 0).all(0)
        g = t.sigmoid(-m) / n
        f = dc @ g
        pjump = h * f * (T0 + e * dt) + h * ((cc + c * cv) * g).sum(0) / B
        tjump = h * f * (P0 + e * dp)
        qjump = h * ((ac + a * av) * g).sum(0) / B
        dv.add_((A.T @ g) * (h * scale * Q) + (C.T @ g) * (h * scale * P))
        dp.add_(pjump)
        dt.add_(tjump)
        dq.add_(qjump)


stream = t.cuda.Stream()
stream.wait_stream(t.cuda.current_stream())
with t.cuda.stream(stream):
    block()
stream.synchronize()
graph = t.cuda.CUDAGraph()
with t.cuda.graph(graph):
    block()
for y in (dp, dt, dq, dv):
    y.zero_()
best = t.full_like(h, -1, dtype=t.long)
ts = t.arange(N, device="cuda")[:, None]
for j in range(0, cap, N):
    graph.replay()
    found = t.where(hit, ts + j, cap + N).amin(0)
    best = t.where((best < 0) & (found < cap), found, best)
    if j + N in (32768, 131072, 524288) or j + N >= cap:
        hits = best.cpu().numpy().reshape(R0.shape)
        print(
            ds,
            mode,
            j + N,
            np.where(hits >= 0, hits, cap + 1).min(1).tolist(),
            flush=True,
        )
        np.savez(sys.argv[4], R=R0, kappa=ks, hits=hits, horizon=min(j + N, cap))
