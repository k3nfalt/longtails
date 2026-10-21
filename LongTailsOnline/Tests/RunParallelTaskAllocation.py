"""Reproducible simulations; these do not replace the missing Comparator certificate."""

from __future__ import annotations

import argparse
import importlib.util
import json
import random
import sys
from dataclasses import asdict
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / "Algorithms/ParallelTaskAllocation.py"
SPEC = importlib.util.spec_from_file_location("parallel_task_allocation", SOURCE)
ata = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ata
SPEC.loader.exec_module(ata)


def run(family: str, horizon: int, seed: int) -> dict:
    if family == "sparse":
        means, B, sigma = [0.375, 0.70] + [0.75] * 6, 2, 0.25
        low, high = 0.5, 1.0
    elif family == "large":
        delta = 0.0625 / (4 * horizon) ** 0.5
        means, B, sigma = [0.625 - delta / 2] + [0.5] * 7, 32, 0.25
        low, high = 0.5, 1.0
    elif family == "rare_times_above_one":
        means, B, sigma = [0.005, 0.01, 0.03, 0.06, 0.1, 0.2, 0.4, 0.9], 3, 2.0
        low, high = 0.001, 4.001
    elif family == "deterministic":
        means, B, sigma = [0.02, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9, 1.0], 32, 0.0
        low = high = None
    else:
        raise ValueError(family)
    n = len(means)
    config = ata.Public(n, B, horizon, sigma)
    policy = ata.ParallelTaskAllocation(config)
    generators = [random.Random((seed + 1) * 100003 + i) for i in range(n)]
    best = ata.proxy(means, ata.ras(means, B))
    total = 0.0
    checkpoints = []
    interval_violations = 0
    maximum_sample = 0.0
    for t in range(1, horizon + 1):
        action = policy.choose()
        feedback = []
        for i, count in enumerate(action):
            if (
                sigma == 0
                or (family == "sparse" and i == 0)
                or (family == "large" and i > 0)
            ):
                row = [means[i]] * count
            else:
                p = (means[i] - low) / (high - low)
                row = [
                    high if generators[i].random() < p else low for _ in range(count)
                ]
            maximum_sample = max(maximum_sample, max(row, default=0.0))
            feedback.append(row)
        policy.observe(feedback)
        total += ata.proxy(means, action) - best
        interval_violations += any(
            not (s - 1e-12 <= mu <= u + 1e-12)
            for s, mu, u in zip(policy.lower, means, policy.upper)
        )
        if t in {1, 10, 100, 1000, horizon}:
            checkpoints.append(
                {"iteration": t, "regret": total, "average_regret": total / t}
            )
    return {
        "family": family,
        "seed": seed,
        "public": asdict(config),
        "hidden_means": means,
        "optimum": best,
        "maximum_observation": maximum_sample,
        "regret": total,
        "average_regret": total / horizon,
        "interval_violation_rounds": interval_violations,
        "checkpoints": checkpoints,
        "execution": policy.report(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=5000)
    parser.add_argument("--seeds", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.seeds < 1:
        parser.error("seeds must be positive")
    results = []
    for family in ["sparse", "large", "rare_times_above_one", "deterministic"]:
        for seed in range(args.seeds):
            result = run(family, args.horizon, seed)
            results.append(result)
            print(
                f"{family} seed={seed}: average proxy regret={result['average_regret']:.6g}; "
                f"completed phases={len(result['execution']['phases']) - int(bool(result['execution']['phases']) and not result['execution']['phases'][-1]['finished'])}",
                flush=True,
            )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps({"formal_regret_certified": False, "runs": results}, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
