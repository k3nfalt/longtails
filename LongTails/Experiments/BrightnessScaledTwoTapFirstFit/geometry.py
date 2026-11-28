"""Check the supplied primal and dual contrast-margin witnesses on the ordered rows."""

import argparse
from pathlib import Path

import numpy as np


def check(path):
    sample = np.load(path)
    witness = np.load(Path(__file__).with_name(f"geometry-{path.stem}.npz"))
    x = sample["levels"][sample["codes"]]
    n, d = x.shape
    shifted = np.roll(x, 1, axis=1)
    contrast = (x - shifted) / np.sqrt(2)
    smooth = (x + shifted) / np.sqrt(2)
    brightness = smooth.mean(1) * np.sqrt(d)
    smooth -= smooth.mean(1, keepdims=True)
    u, dual = witness["unit_separator"], witness["simplex_dual"]
    assert np.all(dual >= 0) and np.isclose(dual.sum(), 1)
    values = {
        "gamma": (contrast @ u).min() / np.linalg.norm(u),
        "dual_upper": np.linalg.norm(dual @ contrast) / dual.sum(),
        "J": (np.linalg.norm(contrast, axis=1) + np.linalg.norm(smooth, axis=1)).max(),
        "D": abs(brightness).max(),
        "mu": min(np.maximum(brightness, 0).mean(), np.maximum(-brightness, 0).mean()),
    }
    for name, value in values.items():
        np.testing.assert_allclose(value, witness[name], atol=1e-7, rtol=1e-6)
    print(path.stem, n, d, values)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sample", type=Path)
    check(parser.parse_args().sample)
