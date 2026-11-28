import hashlib

import numpy as np


def read_native(path):
    f = np.load(path)
    rows = (
        np.rint(255 * f["levels"][f["codes"]]).astype(np.int64)
        if "levels" in f
        else f["signed_pixels"].astype(np.int64)
    )
    assert rows.shape == (5000, 3072) and np.all(rows >= -255) and np.all(rows <= 255)
    v = f["v0"]
    c = f["c0"]
    assert c.shape == (2,) and v.shape == (3072,)
    expected = [
        "d7d5c570ffaa32039f6d85a04fa701e3eb1dd3d833a4b1ef32650b7a6ce5033c",
        "afc856f9bb3412ad14d6dc82cbda782af25fd8f60c6c16acfa2626545457f9cf",
        "7edadd626466ed037ecadd1fd62acf50372f8b27a68a68239e44a8c398ce4617",
    ]
    parts = [rows.astype("<i2"), (c * 2**24).astype("<i8"), (v * 2**30).astype("<i8")]
    assert [hashlib.sha256(x.tobytes()).hexdigest() for x in parts] == expected
    assert np.array_equal(c, parts[1] * 2.0**-24) and np.array_equal(
        v, parts[2] * 2.0**-30
    )
    return rows, v, c
