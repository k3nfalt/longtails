"""Reproduce the CIFAR panel with the paper's per-model grids in FP32."""

import argparse
import math

import matplotlib.pyplot as plt
import numpy as np
import torch


def simulate(rows, rates, nlinear, seed, horizon):
    n, d = rows.shape
    torch.manual_seed(seed)
    readout = torch.rand((d, 1)).mul_(2 / math.sqrt(d)).sub_(1 / math.sqrt(d))
    taps = torch.rand((2, 1)).mul_(2 / math.sqrt(2)).sub_(1 / math.sqrt(2))
    size = len(rates)
    v = readout.repeat(1, size).cuda()
    c = taps.repeat(1, size).cuda()
    learn = torch.arange(size, device="cuda") >= nlinear
    eta = torch.tensor(rates, device="cuda") / n
    block_size = 32
    counts = torch.empty((block_size, size), dtype=torch.int32, device="cuda")

    def reset():
        v.copy_(readout.repeat(1, size))
        c.copy_(taps.repeat(1, size))
        c[0, :nlinear] = 1
        c[1, :nlinear] = 0

    def scores():
        return rows @ (c[0] * v + c[1] * v.roll(-1, 0))

    def block():
        for t in range(block_size):
            m = scores()
            counts[t].copy_((m > 0).sum(0))
            g = rows.T @ torch.sigmoid(-m)
            shifted = g.roll(1, 0)
            dv = c[0] * g + c[1] * shifted
            dc = torch.stack([(g * v).sum(0), (shifted * v).sum(0)]) * learn
            v.add_(dv * eta)
            c.add_(dc * eta)

    reset()
    stream = torch.cuda.Stream()
    stream.wait_stream(torch.cuda.current_stream())
    with torch.cuda.stream(stream):
        block()
    stream.synchronize()
    reset()
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        block()
    result = np.empty((horizon + 1, size), dtype=np.int32)
    for t in range(0, horizon, block_size):
        graph.replay()
        result[t : t + block_size] = counts.cpu().numpy()
    result[-1] = (scores() > 0).sum(0).cpu().numpy()
    return result, taps.numpy().ravel().tolist()


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("cohort")
parser.add_argument("output")
args = parser.parse_args()
raw = np.load(args.cohort)["rows"]
if raw.shape != (5000, 3072):
    parser.error("Prepare the CIFAR-10 airplane/car cohort first")
sign = np.repeat([-1, 1], 2500)[:, None]
pixels = np.rint((raw * sign + 1) * 127.5).astype(np.uint8)
rows = torch.from_numpy(pixels).cuda().float().div_(255).mul_(2).sub_(1)
rows[:2500].neg_()
rates = [
    [0.001, 0.01, 0.1, 1, 10, 100],
    [1 / 64, 1 / 32, 1 / 16, 1 / 8, 1 / 4, 1 / 2, 1],
]
torch.set_float32_matmul_precision("highest")
counts, _ = simulate(rows, rates[0] + rates[1], len(rates[0]), 20261125, 400000)
fig, axs = plt.subplots(1, 2, figsize=(11, 4), sharey=True, constrained_layout=True)
for ax, start, etas, title in zip(
    axs, [0, 6], rates, ["Linear readout", "Two learned taps and readout"]
):
    for k, eta in enumerate(etas):
        col = counts[:, start + k]
        peak = np.flatnonzero(col == 5000)
        lab = f"{eta:g}"
        ax.plot(
            np.arange(0, len(col), 256),
            col[::256] / 5000,
            linewidth=0.75,
            alpha=0.85,
            label=lab,
        )
        if peak.size:
            ax.scatter(peak[0], 1, s=13, zorder=5)
    ax.set(xlabel="Full-gradient updates", title=title, ylim=(0.77, 1.008))
    ax.ticklabel_format(axis="x", style="sci", scilimits=(3, 3))
    ax.legend(title="Constant step", ncol=2, fontsize=8)
    ax.grid(alpha=0.15)
axs[0].set_ylabel("Fraction of 5,000 training images classified correctly")
fig.savefig(args.output, dpi=180)
