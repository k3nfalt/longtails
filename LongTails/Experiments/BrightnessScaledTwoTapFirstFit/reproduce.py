import argparse
import gzip
import hashlib
import io
import json
import math
from pathlib import Path

import numpy as np
import torch


def load_images(dataset, source, rng):
    if dataset == "cifar":
        import pyarrow.parquet as pq
        from PIL import Image

        table = pq.ParquetFile(source).read()
        labels = np.array(table["label"])
        classes = (0, 1)
    else:
        labels = np.frombuffer(
            gzip.decompress((source / "train-labels-idx1-ubyte.gz").read_bytes()),
            dtype=np.uint8,
            offset=8,
        )
        pixels = np.frombuffer(
            gzip.decompress((source / "train-images-idx3-ubyte.gz").read_bytes()),
            dtype=np.uint8,
            offset=16,
        ).reshape(len(labels), -1)
        classes = (7, 8) if dataset == "mnist" else (5, 7)
    indices = np.concatenate(
        [rng.choice(np.flatnonzero(labels == c), 2500, replace=False) for c in classes]
    )
    if dataset == "cifar":
        pixels = np.stack(
            [
                np.asarray(
                    Image.open(io.BytesIO(table["img"][int(i)].as_py()["bytes"]))
                )
                .transpose(2, 0, 1)
                .reshape(-1)
                for i in indices
            ]
        )
        rows = torch.from_numpy(pixels).cuda().float().div_(255).mul_(2).sub_(1)
        rows[:2500].neg_()
    else:
        rows = (
            torch.from_numpy(
                (pixels[indices].astype(float) / 127.5 - 1)
                * np.where(labels[indices] == classes[0], -1.0, 1.0)[:, None]
            )
            .cuda()
            .float()
        )
    return indices, rows


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


def main():
    p = argparse.ArgumentParser()
    p.add_argument("dataset", choices=["cifar", "mnist", "fashion"])
    p.add_argument("source", type=Path, help="CIFAR Parquet file or IDX gzip directory")
    p.add_argument("out", type=Path)
    p.add_argument("--seed", type=int)
    p.add_argument("--grid", choices=["paper", "matched"], default="paper")
    args = p.parse_args()
    seed = (
        args.seed
        if args.seed is not None
        else (20261125 if args.dataset == "cifar" else 20261127)
    )
    torch.set_float32_matmul_precision("highest")
    indices, rows = load_images(args.dataset, args.source, np.random.default_rng(seed))
    if args.grid == "paper":
        linear = [10.0**i for i in range(-3, 3)]
        learned = [2.0**i for i in range(-6, 1)]
    else:
        linear = [2.0 ** (i / 2) for i in range(-20, 15)]
        learned = linear
    counts, taps = simulate(rows, linear + learned, len(linear), seed, 400000)
    hits = [
        int(t[0]) if t.size else None
        for t in (np.flatnonzero(c == len(indices)) for c in counts.T)
    ]
    args.out.mkdir(parents=True, exist_ok=True)
    np.save(args.out / "indices.npy", indices)
    np.savez_compressed(args.out / "correct.npz", correct=counts)
    summary = dict(
        dataset=args.dataset,
        seed=seed,
        grid=args.grid,
        horizon=400000,
        linear_rates=linear,
        learned_rates=learned,
        hits=hits,
        initial_taps=taps,
        index_sha256=hashlib.sha256(indices.astype("<i8").tobytes()).hexdigest(),
        torch=str(torch.__version__),
        device=torch.cuda.get_device_name(),
    )
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(summary)


if __name__ == "__main__":
    main()
