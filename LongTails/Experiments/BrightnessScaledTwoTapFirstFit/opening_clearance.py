import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from math import gcd

import numpy as np

f = np.load(sys.argv[1])
Z = np.rint(255 * f["levels"][f["codes"]]).astype(np.int64)
n, d = Z.shape
V = np.rint(f["v0"] * 2**30).astype(np.int64)
C = np.rint(f["c0"] * 2**24).astype(np.int64)
assert np.array_equal(V.astype(float) / 2**30, f["v0"]) and np.array_equal(
    C.astype(float) / 2**24, f["c0"]
)
assert d * int(abs(V).max()) * 255 < 2**62
DC = Z.sum(1)
raw = Z @ V
shift = Z @ np.roll(V, -1)
numer = [int(C[0]) * int(x) + int(C[1]) * int(y) for x, y in zip(raw, shift)]
den = 255 * 2**54
m = [Fraction(a, den) for a in numer]
a, b = int(sum(DC[DC > 0])), int(-sum(DC[DC < 0]))
stride = gcd(a, b)
i = min(np.flatnonzero(DC > 0), key=lambda j: m[j] / int(DC[j]))
j = min(np.flatnonzero(DC < 0), key=lambda j: m[j] / int(-DC[j]))
s = (int(-DC[j]) * m[i] + int(DC[i]) * m[j]) / int(DC[i] - DC[j])
# Decimal.exp is correctly rounded (half even); widen each rational contribution by one ulp at each operation via neighboring values.
with localcontext() as ctx:
    ctx.prec = 64
    dn = Decimal(den)
    lo = hi = Decimal(0)
    for ai, mi in zip(DC, numer):
        exp_lower = (Decimal(mi) / dn).next_minus().exp().next_minus()
        h = (Decimal(mi) / dn).next_plus().exp().next_plus()
        low = (Decimal(1) / (1 + h).next_plus()).next_minus()
        high = (Decimal(1) / (1 + exp_lower).next_minus()).next_plus()
        x = Decimal(int(ai))
        v, w = sorted((x * low, x * high))
        lo = (lo + v.next_minus()).next_minus()
        hi = (hi + w.next_plus()).next_plus()
    t = (lo / Decimal(stride)).to_integral_value()
    delta = min(abs(lo - t * stride), abs(hi - t * stride))
    assert lo > t * stride or hi < t * stride
    assert 2 * max(abs(lo - t * stride), abs(hi - t * stride)) < stride
    base = delta / Decimal(n * 255) / Decimal(d).sqrt()
    amp = Decimal(abs(int(C.sum()))) / Decimal(2**24)
    print(
        "brightness integer totals and gcd", a, b, stride, "nearest lattice multiple", t
    )
    print("enclosure of unnormalized opening", lo, hi)
    print("distance native raw", base, "tangent", base * amp)
    print("balanced rows", i, j, int(DC[i]), int(DC[j]), "score", s, float(s))
