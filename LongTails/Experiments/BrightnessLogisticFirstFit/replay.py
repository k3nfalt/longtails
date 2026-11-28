"""Rebuild an ordered signed cohort from its public training split and replay GD."""

import argparse
import gzip
import hashlib
import io
import json
import math
import tarfile
import zipfile
from pathlib import Path

import numpy as np
import torch
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
    np.savez(
        args.output,
        rows=output,
        v=manifest[args.dataset + "_v0"],
        c=manifest[args.dataset + "_c0"],
    )


def fit(args):
    data = np.load(args.sample)
    x, v0, c0 = [
        torch.as_tensor(data[key], device="cuda", dtype=torch.float64)
        for key in ("rows", "v", "c")
    ]
    v0, c0 = v0.ravel(), c0.ravel()
    if args.reflect:
        aux = v0 - v0[0]
        alt = (1 - 2 * (torch.arange(len(aux), device="cuda") % 2)).double()
        aux = aux - alt * (alt @ aux) / len(aux)
        v0 = torch.cat((v0 + aux, (v0 - aux).flip([0]))) / math.sqrt(2)
        x = torch.cat((x, x.flip([1])), dim=1) / math.sqrt(2)
    if args.brightness != 1:
        mask = torch.ones(x.shape[1] // 2 + 1, device="cuda", dtype=torch.float64)
        mask[0] = args.brightness
        x = torch.fft.irfft(torch.fft.rfft(x) * mask, n=x.shape[1]).contiguous()
        u = torch.fft.irfft(torch.fft.rfft(v0) / mask, n=x.shape[1])
        gain = float(u.norm() / v0.norm())
        x *= gain
        v0 = u / gain
    if args.grid == 12:
        rates = sorted(
            set([0.001, 0.01, 0.1, 1, 10, 100] + [2.0**j for j in range(-6, 1)])
        )
    else:
        rates = sorted(
            set(
                [0.001, 0.01, 0.1, 0.125, 1, 10, 100, 1000]
                + [2.0 ** (j / 2) for j in range(-18, 23)]
            )
        )
    m = len(rates)
    eta = x.new_tensor(rates * 2) / len(x)
    v = torch.cat(
        (v0[:, None].repeat(1, m), (v0 / args.gauge)[:, None].repeat(1, m)), 1
    )
    c = (c0 * args.gauge)[:, None].repeat(1, 2 * m)
    if args.baseline == "raw":
        c[0, :m], c[1, :m] = 1.0, 0.0
    elif args.gauge != 1:
        raise ValueError("Frozen baseline uses the original filter and gauge 1")
    vstart, cstart = v.clone(), c.clone()
    block = 96 if args.grid == 12 else 64
    counts = torch.empty((block, 2 * m), dtype=torch.int32, device="cuda")

    def updates():
        for i in range(block):
            margins = x @ (c[0] * v + c[1] * v.roll(-1, 0))
            counts[i].copy_(((margins > 0) & margins.isfinite()).sum(0))
            grad = x.T @ (-margins).sigmoid()
            shifted = grad.roll(1, 0)
            dv = c[0] * grad + c[1] * shifted
            if args.grid == 12:
                dc = torch.stack(((v * grad).sum(0), (v * shifted).sum(0)))[:, m:]
            else:
                dc = torch.stack(
                    (
                        (v[:, m:] * grad[:, m:]).sum(0),
                        (v[:, m:] * shifted[:, m:]).sum(0),
                    )
                )
            v.add_(dv * eta)
            c[:, m:].add_(dc * eta[m:])

    stream = torch.cuda.Stream()
    stream.wait_stream(torch.cuda.current_stream())
    with torch.cuda.stream(stream):
        updates()
    stream.synchronize()
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        updates()
    v.copy_(vstart)
    c.copy_(cstart)
    hits = np.full(2 * m, -1)
    for first in range(0, args.cap + 1, block):
        graph.replay()
        fit_flags = counts.cpu().numpy()[: args.cap - first + 1] == len(x)
        new = (hits < 0) & fit_flags.any(0)
        hits[new] = first + fit_flags.argmax(0)[new]
        if (hits.reshape(2, m) >= 0).any(1).all():
            break
    print(
        json.dumps(
            dict(
                rates=rates,
                hit=hits.reshape(2, m).tolist(),
                through=first + len(fit_flags) - 1,
            )
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("dataset", choices=PAIRS)
    prep.add_argument("source", type=Path)
    prep.add_argument("output", type=Path)
    run = sub.add_parser("fit")
    run.add_argument("sample", type=Path)
    run.add_argument("--grid", type=int, choices=(12, 47), default=47)
    run.add_argument("--brightness", type=float, default=1)
    run.add_argument("--gauge", type=float, default=1)
    run.add_argument("--cap", type=int, default=500000)
    run.add_argument("--reflect", action="store_true")
    run.add_argument("--baseline", choices=["raw", "frozen"], default="raw")
    args = parser.parse_args()
    if args.command == "prepare":
        prepare(args)
    else:
        if args.gauge <= 0 or args.brightness <= 0 or args.cap < 0:
            parser.error("Use positive scales and a nonnegative cap")
        fit(args)
