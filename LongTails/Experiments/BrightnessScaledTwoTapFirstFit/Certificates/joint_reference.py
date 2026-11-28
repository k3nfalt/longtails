import ctypes as ct
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
import torch
from native_data import read_native
from numpy.ctypeslib import ndpointer

b = Path(__file__).parent
root_rate = "sqrt2over8" in sys.argv[3:]
P, T = (2048, 21000) if root_rate else (1024, 23444)
target = Path(sys.argv[2])
target.mkdir(exist_ok=True, parents=True)
H, v0, c0 = read_native(sys.argv[1])
torch.set_default_dtype(torch.float64)
Z = torch.tensor(H, device="cuda", dtype=torch.float64)
n, d = Z.shape
torch.set_num_threads(1)
ptr = ndpointer(dtype=np.float64, flags="C_CONTIGUOUS")
lib = ct.CDLL(str(b / "joint_reference.so"))
assert lib.threads_hp(8) == 8
lib.initialize_hp.argtypes = [ct.c_int] * 3 + [ptr] * 2
lib.initialize_hp.restype = ct.c_int
lib.state_hp.argtypes = [ptr] * 3
lib.posterior_hp.argtypes = [ptr] * 5
lib.update_hp.argtypes = [ptr] * 2
L = lib.initialize_hp(P, n, d, v0, c0)
if root_rate:
    lib.increase_step_sqrt_two()
vf = np.zeros(d)
cf = np.zeros(2)
vi = np.zeros((d, L))
qi = np.zeros((n, L))
m = np.empty(n)
q = np.empty(n)
xv = np.empty((n, 2))
g = np.empty(d)
states = {
    key: np.lib.format.open_memmap(
        target / (key + ".npy"), mode="w+", dtype=np.float64, shape=(T,) + shape
    )
    for key, shape in [
        ("V", (d,)),
        ("C", (2,)),
        ("Q", (n,)),
        ("YV", (n, 2)),
        ("G", (d,)),
    ]
}
start = time.monotonic()
first = None
maxm = -1e200
minm = 1e200
maxN = 0.0
max_abs_all = 0.0
rd = {}
assert max(n, d) * 255 * (2**26 - 1) < 2**53
for t in range(T + 1):
    assert not lib.state_hp(vi, vf, cf)
    vdig = torch.from_numpy(vi).cuda()
    dot = Z @ torch.cat([vdig, vdig.roll(-1, 0)], 1)
    assert not lib.posterior_hp(dot.cpu().numpy(), qi, q, xv, m)
    worst = float(m.min())
    max_abs_all = max(max_abs_all, float(np.abs(m).max()))
    maxN = max(maxN, math.hypot(np.linalg.norm(vf), np.linalg.norm(cf)))
    maxm = max(maxm, worst)
    minm = min(minm, worst)
    if first is None and worst > 0:
        first = t
    if t < T:
        dotg = Z.T @ torch.from_numpy(qi).cuda()
        assert not lib.update_hp(dotg.cpu().numpy(), g)
        states["V"][t] = vf
        states["C"][t] = cf
        states["Q"][t] = q
        states["YV"][t] = xv
        states["G"][t] = g
    if (
        t in [0, 16, 64, 256, 1024, 4096, 8192, 16384, 20000, 23648, 24000, T]
        or t % 2048 == 0
    ):
        rd[t] = {
            "first": first,
            "min_margin": worst,
            "max_worst": maxm,
            "min_worst": minm,
            "max_abs_margin": max_abs_all,
            "max_parameter_norm": maxN,
            "elapsed": time.monotonic() - start,
        }
        print(t, rd[t], flush=True)
        (target / "progress.json").write_text(json.dumps(rd, indent=1))
