"""Cold FP64 half-power sweeps of the joint model and score-matched controls."""

import argparse
from pathlib import Path

import numpy as np
import torch as t


def run(sample, mode, cap, output):
    data = np.load(sample)
    x = t.as_tensor(data["levels"][data["codes"]], device="cuda", dtype=t.float64)
    n, d = x.shape
    shift = x.roll(1, 1)
    dc = x.mean(1) * np.sqrt(2 * d)
    contrast = (x - shift) / np.sqrt(2)
    smooth = (x + shift) / np.sqrt(2) - dc[:, None] / np.sqrt(d)
    w = t.as_tensor(data["v0"], device="cuda", dtype=x.dtype)
    tap0, tap1 = data["c0"]
    p0 = (tap0 + tap1) / np.sqrt(2)
    q0 = (tap0 - tap1) / np.sqrt(2)
    rates = t.pow(2.0, t.arange(-20, 27, dtype=x.dtype, device="cuda") / 2)
    k = len(rates)
    if mode in ("tangent", "raw", "raw-original", "frozen", "highpass"):
        features = {
            "raw": x,
            "raw-original": x,
            "frozen": tap0 * x + tap1 * shift,
            "highpass": contrast,
        }.get(mode)
        if mode == "tangent":
            features = t.cat(
                (tap0 * x + tap1 * shift, (x @ w)[:, None], (shift @ w)[:, None]), 1
            )
            start = t.cat((w, w[:2] * 0))
        elif mode == "raw":
            start = w * tap0 + w.roll(-1, 0) * tap1
        else:
            start = w
        weights = start[:, None].repeat(1, k).contiguous()
        offset = (
            ((tap0 * (x @ w) + tap1 * (shift @ w)) - features @ start)[:, None]
            if mode == "highpass"
            else 0
        )
        states = [weights]
        initial = [weights.clone()]

        def update():
            margins = features @ weights + offset
            weights.add_((features.T @ t.sigmoid(-margins)) * (rates / n))
            return margins

        block = 64
    else:
        v0 = w - w.mean()
        t0 = w.mean() * np.sqrt(d)
        ca = (contrast @ v0)[:, None]
        sm = (smooth @ v0)[:, None]
        m0 = q0 * ca + p0 * sm + dc[:, None] * (p0 * t0)
        dv = t.zeros((d, k), dtype=x.dtype, device="cuda")
        dp = t.zeros_like(rates)
        dt = dp.clone()
        dq = dp.clone()
        states = [dv, dp, dt, dq]
        initial = [v.clone() for v in states]
        directional = mode.startswith("remove-")
        if directional:
            basis = mode.removeprefix("remove-")
            if basis == "svm":
                archive = np.load(
                    Path(__file__).with_name("geometry-" + sample.stem + ".npz")
                )
                unit = t.as_tensor(
                    archive["unit_separator"], dtype=x.dtype, device="cuda"
                )
            elif basis == "mean":
                unit = contrast.mean(0)
            else:
                unit = t.as_tensor(
                    np.random.default_rng(271828).normal(size=d),
                    dtype=x.dtype,
                    device="cuda",
                )
            unit = unit / unit.norm()
            projection = contrast @ unit
        a = int("a" in mode)
        c = int("c" in mode)
        b = int("b" in mode)

        def update():
            av = contrast @ dv
            cv = smooth @ dv
            if directional:
                corrected = av - projection[:, None] * (unit @ dv)
                margins = (
                    m0
                    + av * q0
                    + cv * (p0 + dp)
                    + ca * dq
                    + sm * dp
                    + dc[:, None] * (p0 * dt + t0 * dp + dp * dt)
                    + corrected * dq
                )
                g = t.sigmoid(-margins) / n
                f = dc @ g
                pstep = f * (t0 + dt) + ((sm + cv) * g).sum(0)
                tstep = f * (p0 + dp)
                qstep = ((ca + corrected) * g).sum(0)
                ag = contrast.T @ g
                dv.add_(
                    ag * (rates * q0)
                    + (smooth.T @ g) * (rates * (p0 + dp))
                    + (ag - unit[:, None] * (projection @ g)) * (rates * dq)
                )
            else:
                q = q0 + a * dq
                p = p0 + c * dp
                margins = (
                    m0
                    + av * q
                    + cv * p
                    + ca * dq
                    + sm * dp
                    + dc[:, None] * (p0 * dt + t0 * dp + b * dp * dt)
                )
                g = t.sigmoid(-margins) / n
                f = dc @ g
                pstep = f * (t0 + b * dt) + ((sm + c * cv) * g).sum(0)
                tstep = f * (p0 + b * dp)
                qstep = ((ca + a * av) * g).sum(0)
                dv.add_((contrast.T @ g) * (rates * q) + (smooth.T @ g) * (rates * p))
            dp.add_(pstep * rates)
            dt.add_(tstep * rates)
            dq.add_(qstep * rates)
            return margins

        block = 32
    fitted = t.empty((block, k), device="cuda", dtype=t.bool)

    def replay_block():
        for i in range(block):
            margins = update()
            fitted[i] = t.isfinite(margins).all(0) & (margins > 0).all(0)

    stream = t.cuda.Stream()
    stream.wait_stream(t.cuda.current_stream())
    with t.cuda.stream(stream):
        replay_block()
    stream.synchronize()
    graph = t.cuda.CUDAGraph()
    with t.cuda.graph(graph):
        replay_block()
    for v, start in zip(states, initial, strict=True):
        v.copy_(start)
    hits = t.full_like(rates, -1, dtype=t.long)
    times = t.arange(block, device="cuda")[:, None]
    for j in range(0, cap, block):
        graph.replay()
        first = t.where(fitted, times + j, cap + block).amin(0)
        hits = t.where((hits < 0) & (first < cap), first, hits)
    np.savez(output, hits=hits.cpu().numpy(), rates=rates.cpu().numpy(), cap=cap)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sample", type=Path)
    parser.add_argument(
        "mode",
        choices=[
            "raw",
            "raw-original",
            "tangent",
            "frozen",
            "highpass",
            "abc",
            "a",
            "b",
            "c",
            "ac",
            "ba",
            "bc",
            "remove-svm",
            "remove-mean",
            "remove-random",
        ],
    )
    parser.add_argument("cap", type=int, help="Check iterates 0 through cap-1")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    run(args.sample, args.mode, args.cap, args.output)
