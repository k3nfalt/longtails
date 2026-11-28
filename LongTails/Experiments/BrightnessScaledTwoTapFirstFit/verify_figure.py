import hashlib
import json
from pathlib import Path

import numpy as np

root = Path(__file__).parent
reference = json.loads((root / "expected.json").read_text())
for grid, summary in reference.items():
    run = root / f"rerun-{grid}"
    counts = np.load(run / "correct.npz")["correct"]
    digest = hashlib.sha256(counts.astype("<i4").tobytes()).hexdigest()
    assert digest == summary["count_sha256"], (grid, digest)
    np.testing.assert_array_equal(
        np.load(run / "indices.npy"), np.load(root / "indices.npy")
    )
    print(f"{grid} verified {counts.size:,} counts")
