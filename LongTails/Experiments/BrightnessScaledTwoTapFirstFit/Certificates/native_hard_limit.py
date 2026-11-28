import math
import sys
from decimal import Decimal as D
from decimal import localcontext

import numpy as np
import torch as t
from native_data import read_native

K, v0, c0 = read_native(sys.argv[1])
mode = sys.argv[2]
assert mode in ("raw", "tangent")
n, d = K.shape
v = (v0 * 2**30).astype(np.int64)
s = np.roll(v, -1)
a, b = (c0 * 2**24).astype(np.int64).tolist()


def mat(A, x):
    # exact integer matrix-vector product using 18-bit limbs by bounded int64 GEMV.
    out = np.zeros(A.shape[0], dtype=object)
    y = np.asarray(x, dtype=object)
    sg = np.sign(y).astype(np.int64)
    y = np.abs(y)
    shift = 0
    while np.any(y):
        col = (y % 2**18).astype(np.int64) * sg
        out += (A @ col).astype(object) << shift
        y //= 2**18
        shift += 18
    return out


w0 = (a * v + b * s) if mode == "tangent" else v
bits = 54 if mode == "tangent" else 30
score0 = mat(K, w0.astype(object))
assert np.array_equal(score0, K @ w0)
with localcontext() as c:
    c.prec = 80
    q0 = np.array(
        [
            int(
                (
                    (1 / (1 + (D(int(z)) / D(255 * 2**bits)).exp())) * D(2**96)
                ).to_integral_value()
            )
            for z in score0
        ],
        dtype=object,
    )


def M(x):
    if mode == "raw":
        return x * (2**60)
    return (
        ((a * a + b * b) * x + a * b * (np.roll(x, 1) + np.roll(x, -1))) * (2**12)
        + v.astype(object) * sum(v.astype(object) * x)
        + s.astype(object) * sum(s.astype(object) * x)
    )


G0 = mat(K, M(mat(K.T.copy(), q0)))
den = 255**2 * n * 2**60  # normalized margin initial hard accumulator m1
opening = np.array([float(int(x) / (den * 2**96)) for x in G0])
assert np.max(np.abs(opening)) < 1000
Z = t.tensor(K, device="cuda", dtype=t.float64)
vv = t.tensor(v / 2.0**30, device="cuda")
sv = vv.roll(-1)
ca, cb = c0
init = t.tensor(opening, device="cuda")
C = t.zeros_like(vv)
r = t.zeros(n, dtype=t.float64, device="cuda")
best = 1.0e10
worst = -1.0e10
touched = 0
T = 24576
u = 2**-53
for k in range(1, T + 1):
    # integer C updated by matvec on 0/1 entries, each partial sum fits exactly.
    cv = (
        C
        if mode == "raw"
        else ca * cb * (C.roll(1) + C.roll(-1))
        + (ca * ca + cb * cb) * C
        + vv * (vv @ C)
        + sv * (sv @ C)
    )
    m = init + Z @ cv / float(255**2 * n)
    # Conservative uniform roundoff from M C and row dot. ||v||<1, ||K_i||<=255sqrt(d).
    er = (2.0e-12 if mode == "raw" else 2.0e-13) + (9 * d * u / (255 * n)) * math.sqrt(
        d
    ) * float(C.norm()) * (1 + 1e-7)
    mask = m < 0
    lo = float(m.abs().min()) - er
    upperbad = float(m.min()) + er
    if lo <= 1.0e-12:
        indices = t.nonzero(m.abs() <= er + 1.0e-12).flatten().cpu().numpy()
        ci = C.cpu().long().numpy().astype(object)
        numer = mat(K[indices], M(ci)) * (2**96) + G0[indices]
        exact = np.array([float(int(y) / (den * 2**96)) for y in numer])
        assert np.min(abs(exact)) > 1.0e-14
        # use exact signs and conservative lower bound for all rows: omitted rows only known >1e-12
        mask[t.as_tensor(indices, device="cuda")] = t.as_tensor(
            exact < 0, device="cuda"
        )
        lo = min(1.0e-12, float(np.min(abs(exact))) * (1 - 1e-7) - 1.0e-20)
        touched += len(indices)
    best = min(best, lo)
    worst = max(worst, upperbad)
    assert upperbad < 0 and best > 0, (k, upperbad, best)
    C.add_(Z.T @ mask.to(t.float64))
    if k in [1, 256, 1024, 8192, 16384, T]:
        print(k, best, worst, touched, flush=True)
