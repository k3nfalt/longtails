"""Rebuild an ordered signed cohort from its public training split and replay GD."""

import argparse
import gzip
import hashlib
import io
import tarfile
import zipfile
from pathlib import Path

import numpy as np
from PIL import Image

PAIRS = {
    "cifar": (0, 1),
    "euro": (3, 7),
    "gisette": (-1, 1),
    "fashion57n2000": (5, 7),
    "fashion79n2000": (7, 9),
    "mnist78": (7, 8),
}


def samples(case, source):
    low, high = PAIRS[case]
    if case == "gisette":
        with zipfile.ZipFile(source) as archive:
            labels = np.loadtxt(archive.open("GISETTE/gisette_train.labels"))
            with archive.open("GISETTE/gisette_train.data") as images:
                for label, line in zip(labels, images, strict=True):
                    yield label * (np.fromstring(line, sep=" ") * 2 / 999 - 1)
        return
    if case == "cifar" and source.suffix == ".parquet":
        import pyarrow.parquet as pq

        for batch in pq.ParquetFile(source).iter_batches(
            columns=["img", "label"], batch_size=256
        ):
            for image, label in zip(*batch.columns, strict=True):
                label = label.as_py()
                if label in (low, high):
                    with Image.open(io.BytesIO(image.as_py()["bytes"])) as rgb:
                        yield pixels(
                            np.asarray(rgb).transpose(2, 0, 1).ravel(), label == high
                        )
        return
    if case == "cifar":
        with tarfile.open(source, "r:gz") as archive:
            for entry in archive:
                if not Path(entry.name).name.startswith("data_batch_"):
                    continue
                rows = np.frombuffer(archive.extractfile(entry).read(), np.uint8)
                for row in rows.reshape(-1, 3073):
                    if row[0] in (low, high):
                        yield pixels(row[1:], row[0] == high)
        return
    if case == "euro":
        with zipfile.ZipFile(source) as archive:
            names = [
                p
                for p in archive.namelist()
                if p.lower().endswith(".jpg") and "__MACOSX" not in p
            ]
            classes = sorted({Path(p).parent.name for p in names})
            for p in names:
                label = classes.index(Path(p).parent.name)
                if label in (low, high):
                    with Image.open(io.BytesIO(archive.read(p))) as image:
                        yield pixels(
                            np.asarray(image.convert("RGB")).transpose(2, 0, 1).ravel(),
                            label == high,
                        )
        return
    labels = np.frombuffer(
        gzip.decompress((source / "train-labels-idx1-ubyte.gz").read_bytes()),
        np.uint8,
        offset=8,
    )
    images = np.frombuffer(
        gzip.decompress((source / "train-images-idx3-ubyte.gz").read_bytes()),
        np.uint8,
        offset=16,
    )
    for label, image in zip(labels, images.reshape(-1, 784), strict=True):
        if label in (low, high):
            yield pixels(image, label == high)


def pixels(image, positive):
    q = 2 * image.astype(np.int16) - 255
    return (q if positive else -q).astype(np.float64) / 255


def prepare(args):
    manifest = np.load(Path(__file__).with_name("Draws.npz"))
    desired = manifest[args.dataset + "_rows"]
    positions = {}
    for index, digest in enumerate(desired):
        positions.setdefault(digest.tobytes(), []).append(index)
    output = None
    for row in samples(args.dataset, args.source):
        row = np.ascontiguousarray(row, dtype="<f8")
        row[row == 0] = 0
        indices = positions.pop(hashlib.sha256(row.tobytes()).digest(), [])
        if indices:
            if output is None:
                output = np.empty((len(desired), len(row)), np.float64)
            output[indices] = row
        if not positions:
            break
    if positions:
        raise ValueError(f"{len(positions)} distinct signed rows missing from source")
    levels, codes = np.unique(output.ravel(), return_inverse=True)
    np.savez_compressed(
        args.output,
        levels=levels,
        codes=codes.reshape(output.shape).astype(np.min_scalar_type(len(levels) - 1)),
        v0=manifest[args.dataset + "_v0"],
        c0=manifest[args.dataset + "_c0"],
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dataset", choices=sorted(PAIRS))
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    prepare(parser.parse_args())
