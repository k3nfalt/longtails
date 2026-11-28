"""Generate the fixed-point reference; run native_transport.py to certify it."""

import ctypes as c
import json
import math
import os
import sys
import time
from pathlib import Path

import numpy as np
import torch
from native_data import read_native
from numpy.ctypeslib import ndpointer

root = Path(__file__).parent
input_path, mode, work = sys.argv[1:4]
P, rate, T, th = sys.argv[4:]
P, T, th = map(int, (P, T, th))
root_power = {"sqrt8": 3, "sqrt2over8": -5}.get(rate)
eta = 2.0 ** (root_power / 2) if root_power is not None else int(rate)
assert (mode == "tangent" and eta in (100, 512)) or (
    mode == "raw" and rate in ("512", "sqrt8", "sqrt2over8")
)
path = Path(work)
path.mkdir(exist_ok=True, parents=True)
torch.set_num_threads(1)
H, v, coeff = read_native(input_path)
c0, c1 = coeff
Z = torch.as_tensor(H, device="cuda", dtype=torch.float64)
n, d = Z.shape
v0 = (
    np.ascontiguousarray(c0 * v + c1 * np.roll(v, -1))
    if mode == "tangent"
    else v.copy()
)
assert max(n, d) * 255 * (2**26 - 1) < 2**53
li = c.CDLL(str(root / "native_reference.so"))
a = ndpointer(dtype=np.float64, flags="C_CONTIGUOUS")
li.init.argtypes = [c.c_int] * 5 + [a]
li.state.argtypes = [a]
li.posterior.argtypes = [a] * 4
li.update.argtypes = [a]
li.save.argtypes = [c.c_char_p, c.c_int]
tag = "sqrt8" if rate == "sqrt8" else ("raw" if mode == "raw" else "tangent" + rate)
sched = json.loads((root / "precision_pilot.json").read_text())[tag]
tp = np.array([0] + list(map(int, sched)))
gp = np.array([0.0] + list(sched.values()))
li.precision_change.argtypes = [c.c_int]
li.set_threads.argtypes = [c.c_int]
curP = P
L = li.init(P, n, d, 1 if root_power is not None else eta, th, v0)
li.setup_metric.argtypes = [
    ndpointer(dtype=np.int64, flags="C_CONTIGUOUS"),
    c.c_long,
    c.c_long,
]
if mode == "tangent":
    li.setup_metric((v * 2**30).astype(np.int64), round(c0 * 2**24), round(c1 * 2**24))
else:
    li.setup_metric(np.zeros(d, dtype=np.int64), 2**24, 0)
if root_power is not None:
    li.use_sqrt_rate(root_power)
V = np.empty((d, L))
Qd = np.empty((n, L))
q = np.empty(n)
m = np.empty(n)
info = path / "progress.json"
worst = -math.inf
maxm = 0.0
saved = 0
prev_t = 0.0
hist = {}
t0 = time.monotonic()
if info.exists():
    hist = json.loads(info.read_text())
    saved = int(list(hist)[-1])
    v = hist[str(saved)]
    curP = v["P"]
    L = li.precision_change(curP)
    V = np.empty((d, L))
    Qd = np.empty((n, L))
    assert li.save(os.fsencode(path / f"V-{saved % 512}.gmp"), 1) == 0
    worst = v["max_min_margin"]
    maxm = v["max_abs_margin"]
    prev_t = v["elapsed"]
Q = np.lib.format.open_memmap(
    path / "Q.npy", mode="r+" if saved else "w+", dtype=np.float64, shape=(T, n)
)
vprobe = torch.from_numpy(v0.copy()).cuda()
for t in range(saved, T + 1):
    if not t % 256:
        base, ratio = (8192, 0.64) if rate == "sqrt8" and t > 768 else (P, 0.85)
        nxt = (
            P
            if rate == "sqrt2over8"
            else max(768, base - int(ratio * np.interp(t, tp, gp) // 64) * 64)
        )
        if nxt < curP:
            curP = nxt
            L = li.precision_change(curP)
            V = np.empty((d, L))
            Qd = np.empty((n, L))
        if (path / "threads.txt").exists():
            li.set_threads(int((path / "threads.txt").read_text()))
    assert not li.state(V)
    assert not li.posterior((Z @ torch.from_numpy(V).cuda()).cpu().numpy(), Qd, q, m)
    worst = max(worst, float(m.min()))
    maxm = max(maxm, float(np.abs(m).max()))
    if t < min(12, T):
        mm = (Z @ vprobe / 255).cpu().numpy()
        assert np.max(np.abs(m - mm)) < 1e-6, (t, m[:3], mm[:3])
        gg = (
            eta
            * (Z.T @ torch.from_numpy(np.exp(-np.logaddexp(0, mm))).cuda())
            / (255 * n)
        )
        vv = torch.from_numpy(v).cuda()
        ss = vv.roll(-1)
        vprobe += (
            (
                (c0 * c0 + c1 * c1) * gg
                + c0 * c1 * (gg.roll(-1) + gg.roll(1))
                + vv * (vv @ gg)
                + ss * (ss @ gg)
            )
            if mode == "tangent"
            else gg
        )
    if t % 256 == 0 or t == T:
        dt = prev_t + time.monotonic() - t0
        dest = path / f"V-{t % 512}.gmp"
        tmp = path / "v-swap.gmp"
        assert not li.save(os.fsencode(tmp), 0)
        os.replace(tmp, dest)
        np.save(path / f"margins-{t:05d}.npy", m)
        Q.flush()
        hist[t] = {
            "max_min_margin": worst,
            "max_abs_margin": maxm,
            "elapsed": dt,
            "steps": t,
            "P": curP,
        }
        itmp = path / "temp.json"
        itmp.write_text(json.dumps(hist, indent=1))
        os.replace(itmp, info)
        if t % 1024 == 0 or t == T:
            print(eta, P, t, worst, maxm, dt, flush=True)
    if t < T:
        Q[t] = q
        assert not li.update((Z.T @ torch.from_numpy(Qd).cuda()).cpu().numpy())
