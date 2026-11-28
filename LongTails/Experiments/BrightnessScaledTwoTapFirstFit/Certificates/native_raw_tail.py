import hashlib
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from native_data import read_native

k = 15360
target = 24576
eta = F(2828427124746191, 10**15) if "sqrt8" in sys.argv[3:] else F(512)
if "sqrt2over8" in sys.argv[3:]:
    eta = F(176776695296637, 10**15)
    assert 32 * eta**2 >= 1
else:
    assert eta * eta >= 8
H, _, _ = read_native(sys.argv[1])
n, d = H.shape
p = Path(sys.argv[2])
y = np.load(Path(__file__).with_name("raw_tail_dual.npz"))["counts"]
assert H.max() <= 255 and H.min() >= -255 and y.shape == (n,) and np.all(y >= 0)


def mat(A, x):
    res = np.zeros(A.shape[0], dtype=object)
    sg = np.sign(x).astype(np.int64)
    x = abs(np.asarray(x, dtype=object))
    j = 0
    while np.any(x):
        limb = (x % 2**18).astype(np.int64) * sg
        assert A.shape[1] * 255 * 2**18 < 2**63
        res += (A @ limb).astype(object) << j
        x //= 2**18
        j += 18
    return res


print("sha256", hashlib.sha256(y.astype("<i8").tobytes()).hexdigest(), flush=True)
u = mat(H.T.copy(), y)
g = mat(H, u)
cap = F(sum(max(0, int(c)) for c in g), 255**2 * n)
print("cap", str(cap), flush=True)

a = json.loads((p / "audit.json").read_text())[str(k)]
h = json.loads((p / "progress.json").read_text())[str(k)]
assert (
    a["max_param_error_log2"] < math.log2(1e-13)
    and h["max_min_margin"] < -1e-5
    and h["max_abs_margin"] < 1e6
)
m = np.load(p / f"margins-{k:05d}.npy")
# Per-coordinate signed margin perturbation <= 56 * 1e-13 + 2^-32 when MPFR margin < 1e6.
er = F(56, 10**13) + F(1, 2**32)
at = sum(F(float(z)) * int(c) for z, c in zip(m, y)) + int(y.sum()) * er
# λ^T X theta increases at most η cap per update with q in [0,1]^n.
print("debt", str(at), "last certified step", k + int((-at) // (eta * cap)), flush=True)
assert at + (target - k) * eta * cap < 0
