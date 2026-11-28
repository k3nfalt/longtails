"""Check the hard raw orbit clearance and the reflected spatial margin on pixel integers."""

import argparse
from pathlib import Path

import numpy as np
from flint import arb, ctx

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("dataset")
parser.add_argument("cohort")
args = parser.parse_args()
ctx.prec = 160
dsden = 999 if args.dataset == "gisette" else 255
data = np.load(args.cohort)
Z = np.rint(data["rows"] * dsden).astype(np.int64)
n, d = Z.shape
ui = np.load(Path(__file__).with_name("Separators.npz"))[args.dataset]
du = ui - np.roll(ui, -1)
folded = du[:d] + du[d:][::-1]
assert int(abs(folded).max()) * int(abs(Z).max()) * d < 2**63
assert int(abs(ui).max()) ** 2 * len(ui) < 2**63
minimum = int((Z @ folded).min())
assert minimum > 0
print(
    "Reflected difference-row margin",
    arb(minimum) / (2 * dsden * arb(int(ui @ ui)).sqrt()),
)
vo = data["v"].ravel()
frac = [float(a).as_integer_ratio() for a in vo]
den = max(b for a, b in frac)
v = np.array([a * (den // b) for a, b in frac], dtype=np.int64)
assert int(abs(v).max()) * int(abs(Z).max()) * d < 2**63
scores = Z @ v
D = Z.sum(1)
assert 0 not in D
A = D[D > 0].sum()
B = -D[D < 0].sum()
g = int(np.gcd(A, B))
mass = sum(
    arb(int(di)) / (1 + (arb(int(b)) / (den * dsden)).exp()) for di, b in zip(D, scores)
)
r = mass / g
k = round(float(r.mid()))
dist = abs(r - k)
assert dist > 0 and dist < arb(".5")
# DC-balanced convex combination of two initially failing opposite-DC rows.
ip = np.flatnonzero(D > 0)
im = np.flatnonzero(D < 0)
i = ip[np.argmin(scores[ip] / abs(D[ip]))]
j = im[np.argmin(scores[im] / abs(D[im]))]
x, y = int(D[i]), -int(D[j])
debt = -(arb(y) * int(scores[i]) + arb(x) * int(scores[j])) / ((x + y) * den * dsden)
assert debt > 0
theta = dist * g / (n * dsden * arb(d).sqrt())
print(
    args.dataset,
    "gcd",
    g,
    "fraction of cell",
    dist,
    "signed physical clearance",
    theta,
    "zero-DC pair",
    i,
    j,
    "initial negative margin magnitude",
    debt,
    flush=True,
)

if args.dataset in {"cifar", "gisette"}:
    # Work in units scaled by sqrt(2) to keep the reflected lift rational.
    cone = np.load(Path(__file__).with_name("Separators.npz"))[args.dataset + "_cone"]
    assert np.array_equal(cone, -np.roll(cone[::-1], 1))
    diff = cone - np.roll(cone, -1)
    coeff = diff[:d] + diff[d:][::-1]
    assert int(abs(coeff).max()) * int(abs(Z).max()) * d < 2**63
    shortfall = max(0, 1 - int((Z @ coeff).min()))
    correction = arb(shortfall) / minimum
    seed = [arb(float(x)) for x in vo]
    aux = [x - seed[0] for x in seed]
    offset = sum(x * ((-1) ** i) for i, x in enumerate(aux)) / d
    aux = [x - offset * ((-1) ** i) for i, x in enumerate(aux)]
    tap1, tap2 = map(float, data["c"].ravel())
    sign = 1 if tap1 > tap2 else -1
    lift = [sign * (x + y) for x, y in zip(seed, aux)] + [
        sign * (x - y) for x, y in zip(seed, aux)
    ][::-1]
    odd = [(x - y) / 2 for x, y in zip(lift, [lift[0]] + lift[:0:-1])]
    delta = [
        x - (int(i) + correction * int(j)) / 2**29 for x, i, j in zip(odd, cone, ui)
    ]
    distance = sum(x * x for x in delta).sqrt()
    tap_difference = abs(arb(tap1) - arb(tap2))
    gauge = arb(1.5 if args.dataset == "cifar" else 1.28)
    dc_energy = sum(lift) ** 2 / len(lift)
    energy = sum(x * x for x in lift)
    for contrast in (1, 2, 4):
        gain = (1 - (1 - 1 / arb(contrast) ** 2) * dc_energy / energy).sqrt()
        gap = ((tap_difference * gauge) ** 2 - (distance / (gain * gauge)) ** 2) / 2
        assert gap > 0
        print("Reflected initial squared-balance lower bound", contrast, gap)
