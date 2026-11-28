"""Plot Figure 1 from the reproduced integer accuracy traces."""

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument(
    "input", type=Path, nargs="?", default=root / "rerun-paper/correct.npz"
)
parser.add_argument("output", type=Path, nargs="?", default=root / "figure1.png")
args = parser.parse_args()
counts = np.load(args.input)["correct"]
assert counts.shape == (400001, 13)
panels = [
    ("Raw linear readout", [0.001, 0.01, 0.1, 1, 10, 100], 0),
    (
        "Joint two-tap filter and readout",
        [1 / 64, 1 / 32, 1 / 16, 1 / 8, 1 / 4, 1 / 2, 1],
        6,
    ),
]
colors = ["#0072B2", "#D55E00", "#009E73", "#CC79A7", "#4B488B", "#805500", "#333333"]
styles = ["-", "--", "-.", ":", "-", "--", "-."]
steps = np.arange(len(counts))
fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), sharey=True, constrained_layout=True)
for axis, (title, rates, start) in zip(axes, panels, strict=True):
    for j, rate in enumerate(rates):
        column = counts[:, start + j]
        axis.plot(
            steps,
            column / 5000,
            linewidth=0.8,
            color=colors[j],
            linestyle=styles[j],
            label=f"{rate:g}",
        )
        first = np.flatnonzero(column == 5000)
        if first.size:
            axis.scatter(first[0], 1, s=16, color=colors[j], zorder=5)
    axis.set_xscale("symlog", linthresh=10)
    axis.set(
        xlabel="Full-gradient updates", title=title, xlim=(0, 450000), ylim=(0, 1.025)
    )
    axis.grid(alpha=0.18)
    axis.legend(title="Constant step", loc="lower left", fontsize=8, ncols=2)
axes[0].set_ylabel("Fraction of 5,000 training images classified correctly")
fig.savefig(args.output, dpi=180)
