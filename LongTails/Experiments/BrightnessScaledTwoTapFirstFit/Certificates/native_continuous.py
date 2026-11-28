import json
import sys
from decimal import Decimal, localcontext
from pathlib import Path

import numpy as np
import torch as t
from native_data import read_native

K, v, c = read_native(sys.argv[1])
n, d = K.shape
s = np.roll(K, 1, axis=1)
cv = (c * 2**24).astype(np.int64)
iv = (v * 2**30).astype(np.int64)
Z = t.tensor(
    np.column_stack(
        [
            (cv[0] * K + cv[1] * s) / (255 * 2.0**24),
            (K @ iv) / (255 * 2.0**30),
            (s @ iv) / (255 * 2.0**30),
        ]
    ),
    device="cuda",
)
n, d = Z.shape
u = 2**-53
R = 5.0
assert float(Z.norm(dim=1).max()) * (1 + 1e-7) < R
# Explicit Cholesky residual bounds the spectral radius by 1.3331, so T_h is nonexpansive for every 0<=h<=6.
identity = t.eye(d, device="cuda", dtype=Z.dtype)
G = (Z.T @ Z) / n
B = 1.3331 * identity - G
L = t.linalg.cholesky(B)
res = float((L @ L.T - B).norm()) * (1 + 1e-7)
gn = n * u / (1 - n * u)
gd = d * u / (1 - d * u)
E = res + 1e-7 + gd * float(L.norm()) ** 2 * 1.0001
print("gram", res, E, 1.3331 + E, flush=True)
assert 1.3331 + E < 4 / 3
with localcontext() as ctx:
    ctx.prec = 45
    tab = t.tensor(
        [float(1 / (1 + (Decimal(i) / 512).exp())) for i in range(40 * 512 + 1)],
        device="cuda",
        dtype=Z.dtype,
    )
Rrow = Z.norm(dim=1) * (1 + 1e-7) + 1e-200
rates = (
    [0.0]
    + [1e-6 * 1.16**k for k in range(80) if 1e-6 * 1.16**k < 0.1]
    + list(np.arange(0.1**0.5, 6.0**0.5, 0.024) ** 2)
    + [6.0]
)
h = t.as_tensor(sorted(set(rates)), device="cuda", dtype=t.float64)
z0 = t.tensor(np.r_[v, 0.0, 0.0], device="cuda")
W = z0[:, None].repeat(1, len(h))
cap = t.zeros_like(h) + 1.0e10
mass = t.zeros_like(h)
err = mass.clone()
T = 28688


def st():
    for i in range(8):
        m = Z @ W
        s = m.abs().clamp_max(40)
        j = (s * 512).round().long()
        dx = s - j / 512.0
        q = tab[j]
        b = q * (1 - q)
        q = q + dx * b * (
            -1
            + dx
            * (
                0.5
                - q
                + dx
                * (
                    (-1 + 6 * q - 6 * q * q) / 6
                    + dx * (1 - 14 * q + 36 * q * q - 24 * q * q * q) / 24
                )
            )
        )
        q = t.where(m >= 0, q, 1 - q).clamp(0, 1)
        wn = W.norm(dim=0) * (1 + 1e-7)
        em = (d + 10) * u * R * wn * (1 + 1e-7) + 1e-200
        goodradius = ((-m - em) / Rrow[:, None]).amax(dim=0) * (1 - 1e-9) - 1e-16
        cap.copy_(
            t.minimum(cap, (goodradius - err) / (mass + 1e-100) * (1 - 1e-8) - 1e-16)
        )
        g = Z.T @ q / n
        gerr = R * (6.0e-14 + em / 4 + (n + 150) * u) * (1 + 1e-9) + 1e-200
        gn = g.norm(dim=0) * (1 + 1e-7) + gerr
        err.copy_((err + h * gerr + 4 * u * (wn + h * R)) * (1 + 4 * u) + 1e-100)
        mass.copy_((mass + gn) * (1 + 4 * u) + 1e-100)
        W.add_(g * h)


st()
gr = t.cuda.CUDAGraph()
with t.cuda.graph(gr):
    st()
W.copy_(z0[:, None])
err.zero_()
mass.zero_()
cap.fill_(1.0e10)
for j in range((T + 7) // 8):
    gr.replay()
cent = h.cpu().tolist()
rad = cap.cpu().tolist()
gaps = []
upper = 0.0
for a, b in zip(cent, rad):
    if a - b > upper - 1e-12 and a > 0:
        gaps.append([upper, a - b])
    upper = max(upper, a + b)
print(
    "ncenters,T,firstcap,lastupper,gaps", len(rad), T, rad[0], upper, gaps, flush=True
)
Path(sys.argv[2]).write_text(
    json.dumps({"t": T - 1, "centers": cent, "radii": rad, "gaps": gaps})
)
assert rad[0] > 0 and upper > 6 and not gaps
