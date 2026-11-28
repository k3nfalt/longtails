import math
import sys
from decimal import Decimal, localcontext

import numpy as np
import torch as t
from native_data import read_native

K, v0, c0 = read_native(sys.argv[1])
v0n = (v0 * 2**30).astype(np.int64)
c = (c0 * 2**24).astype(np.int64)
Ks = np.roll(K, 1, axis=1)
raw = c[0] * K + c[1] * Ks
Fs = np.stack([K @ v0n, Ks @ v0n], 1)
assert (
    np.max(np.abs(K)) <= 255
    and K.shape == (5000, 3072)
    and np.max(abs(Fs)) < 2**53
    and np.max(abs(raw)) < 2**53
)
X = t.tensor(
    np.column_stack([raw / (255 * 2.0**24), Fs / (255 * 2.0**30)]), device="cuda"
)
n, d = X.shape
R = math.ceil(float(X.norm(dim=1).max()) * (1 + 1e-8))
u = 2**-53
G = (X @ X.T / n).abs()
G = (G + ((d + 10) * u * R * R / n) * (1 + 1e-7)) * (1 + 1e-7)
with localcontext() as ctx:
    ctx.prec = 45
    tbl = [float(1 / (1 + (Decimal(i) / 512).exp())) for i in range(40 * 512 + 1)]
tab = t.tensor(tbl, device="cuda", dtype=X.dtype)
rates = np.array(
    sorted(
        set([0.001, 0.01, 0.1, 0.125, 1, 10.0] + [2 ** (j / 2) for j in range(-18, 12)])
    )
)
h = t.tensor(rates, device="cuda")
z0 = t.tensor(np.r_[v0, 0.0, 0.0], device="cuda")
W = z0[:, None].repeat(1, len(h))
rho = 0.001
rad = t.zeros_like(h)
maxrad = rad.clone()
maxm = rad.clone() - 1e20


def block():
    for k in range(16):
        m = X @ W
        s = m.abs().clamp_max(40)
        idx = (s * 512).round().long()
        dx = s - idx / 512.0
        q = tab[idx]
        b = q * (1 - q)
        # idx is an integer dyadic in an exact float32 range; cast before arithmetic.
        x2 = q * q
        q = q + dx * b * (
            -1
            + dx
            * (
                0.5
                - q
                + dx
                * (
                    (-1 + 6 * q - 6 * x2) / 6
                    + dx * (1 - 14 * q + 36 * x2 - 24 * x2 * q) / 24
                )
            )
        )
        q = t.where(m >= 0, q, 1 - q).clamp(0, 1)
        wn = W.norm(dim=0) * (1 + 1e-7)
        em = (d + 10) * u * R * wn * (1 + 1e-7)
        maxm.copy_(t.maximum(maxm, m.amin(0) + (em + R * rad) * (1 + 1e-7)))
        # Relative density bound follows from |(log(q(1-q)))'|<=1.
        pu = (q * (1 - q) + 6e-14) * (1 + 1e-7)
        pu *= 1 / (1 - (R * rho + em).clamp(max=0.5))
        pu = t.where((R * rho + em) < 0.5, pu, 0.2500000001)
        a = G @ pu
        z = G @ (pu * a) + 1e-98
        eig = ((G @ (pu * z)) / z).amax(0) * (1 + 1e-7) + 1e-55
        gain = t.maximum(
            t.ones_like(eig), (h * (1 + 1e-14) * eig - 1) * (1 + 1e-8) + 1e-12
        )
        defect = h * R * (6e-14 + em / 4 + (n + 100) * u) + 4 * u * (wn + h * R)
        rad.copy_(((gain * rad + defect) * (1 + 1e-9) + 1e-100).clamp_max(1e30))
        maxrad.copy_(t.maximum(maxrad, rad))
        W.add_((X.T @ q) * (h / n))


block()
W.copy_(z0[:, None])
rad.zero_()
maxrad.zero_()
maxm.fill_(-1e20)
graph = t.cuda.CUDAGraph()
with t.cuda.graph(graph):
    block()
W.copy_(z0[:, None])
rad.zero_()
maxrad.zero_()
maxm.fill_(-1e20)
for _ in range(1793):
    graph.replay()
print("T, R", 28688, R)
for j, hj in enumerate(rates):
    print(hj, float(maxrad[j]), float(maxm[j]), bool((maxrad[j] < rho) & (maxm[j] < 0)))
