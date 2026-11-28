import hashlib
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from native_data import read_native

p = Path(sys.argv[2])
certpath = Path(sys.argv[3]) if len(sys.argv) > 3 else p
cert = json.loads((certpath / "first-hit.json").read_text())
k = int(cert["first"])
H, v0, c0 = read_native(sys.argv[1])
n, d = H.shape
c = np.load(p / "C.npy", mmap_mode="r")[k]
v = np.load(p / "V.npy", mmap_mode="r")[k]
u = np.load(Path(__file__).with_name("contrast_direction.npy"))
assert cert["passes"] and cert["first"] == k and float(cert["parameter_error"]) < 1e-14
assert np.array_equal(c0, np.load(p / "C.npy", mmap_mode="r")[0]) and np.array_equal(
    v0, np.load(p / "V.npy", mmap_mode="r")[0]
)


def dyad(x):
    vals = [F(float(a)) for a in x]
    den = max(a.denominator for a in vals)
    return np.array(
        [a.numerator * (den // a.denominator) for a in vals], dtype=object
    ), den


def mat(A, x):
    res = np.zeros(A.shape[0], dtype=object)
    sg = np.sign(x).astype(np.int64)
    x = abs(x)
    j = 0
    while np.any(x):
        limb = (x % 2**18).astype(np.int64) * sg
        assert A.shape[1] * 255 * 2**18 < 2**63
        res += (A @ limb).astype(object) << j
        x //= 2**18
        j += 18
    return res


V, dv = dyad(v)
C, dc = dyad(c)
V0, d0 = dyad(v0)
C0, e0 = dyad(c0)
U, du = dyad(u)
deltaC = F(int(C[0] - C[1]), dc) - F(int(C0[0] - C0[1]), e0)
deltaVU = F(int(V @ U), dv * du) - F(int(V0 @ U), d0 * du)
uu = F(int(U @ U), du**2)
g = deltaC * deltaVU / (2 * uu)
m0 = mat(H, C[0] * V + C[1] * np.roll(V, -1))
m = [F(int(x), 255 * dv * dc) for x in m0]
delta = [g * F(int(x), 255 * du) for x in mat(H, U - np.roll(U, -1))]
short = [a - b for a, b in zip(m, delta)]
er = F(1, 10**8)
assert np.linalg.norm(np.r_[v, c]) < 64 and min(m) > er and min(delta) > er
neg = [i for i, x in enumerate(short) if x < -er]
pos = [i for i, x in enumerate(short) if x > er]
j = min(range(n), key=short.__getitem__)
print(
    "u hash",
    hashlib.sha256(u.astype("<f8").tobytes()).hexdigest(),
    "first",
    k,
    "row",
    j,
    "margin",
    float(min(m)),
    "min uniform boost",
    float(min(delta)),
    "max",
    float(max(delta)),
    "deleted min margin",
    float(short[j]),
    "cert negative + positive",
    len(neg),
    len(pos),
    "coefficient",
    float(g) * 2**0.5 * float(uu) ** 0.5,
    flush=True,
)
# Removing all second-order changes leaves the full initial Jacobian at the same displacement.
a1 = C[0] * e0 - C0[0] * dc
b1 = C[1] * e0 - C0[1] * dc
vchange = V * d0 - V0 * dv
nonlin = [
    F(int(y), 255 * dc * e0 * dv * d0)
    for y in mat(H, a1 * vchange + b1 * np.roll(vchange, -1))
]
tang = [a - b for a, b in zip(m, nonlin)]
add = [a + b for a, b in zip(tang, delta)]
for name, sc in [("tang/t", tang), ("tang+svm", add)]:
    print(name, sum(x < -er for x in sc), min(float(x) for x in sc))


# Exact joint GD increments the readout by η(P C_q + Q A_q).
un = u / np.linalg.norm(u)
sh = np.roll(un, -1)
X = H / 255.0
ar = X @ (un - sh) / math.sqrt(2)
cr = X @ (un + sh) / math.sqrt(2)
votes = np.load(p / "Q.npy", mmap_mode="r")[:k]
aq = votes @ ar / n
cq = votes @ cr / n
taps = np.load(p / "C.npy", mmap_mode="r")[:k]
ps = taps.sum(1) / math.sqrt(2)
qs = (taps[:, 0] - taps[:, 1]) / math.sqrt(2)
h = math.sqrt(2) / 8 if cert["P"] == 2048 else 0.125
vals = h * qs[0] * aq.sum(), h * ((qs - qs[0]) * aq).sum(), h * (ps * cq).sum()
print("readout work (fixed contrast, gain change, smooth)", vals)
assert np.max(abs(taps)) < 64 and np.linalg.norm(v) < 64
assert abs(sum(vals) - (v - v0) @ un) < 1e-6
