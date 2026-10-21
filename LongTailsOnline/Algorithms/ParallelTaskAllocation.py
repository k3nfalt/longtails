"""Research implementation; the stochastic regret theorem is not yet Lean-certified."""

from __future__ import annotations

import heapq
import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterator, Sequence


def ras(
    weights: Sequence[float], batch: int, caps: Sequence[int] | None = None
) -> list[int]:
    """Exact integer minimax oracle for the supplied binary floating-point weights."""
    if batch < 0 or any(not math.isfinite(w) or w < 0 for w in weights):
        raise ValueError("Nonnegative finite weights and batch are required")
    limits = list(caps) if caps is not None else [batch] * len(weights)
    if len(limits) != len(weights) or any(c < 0 for c in limits) or sum(limits) < batch:
        raise ValueError("Insufficient or invalid capacities")
    exact = [Fraction(w) for w in weights]
    queue = [(w, i) for i, w in enumerate(exact) if limits[i]]
    heapq.heapify(queue)
    result = [0] * len(weights)
    for _ in range(batch):
        _, i = heapq.heappop(queue)
        result[i] += 1
        if result[i] < limits[i]:
            heapq.heappush(queue, ((result[i] + 1) * exact[i], i))
    return result


def capacities(
    lower: Sequence[float],
    level: float,
    batch: int,
    active: Sequence[bool] | None = None,
) -> list[int]:
    active = list(active) if active is not None else [True] * len(lower)
    L = Fraction(level)
    return [
        0 if not enabled else batch if s <= 0 else min(batch, L // Fraction(s))
        for s, enabled in zip(lower, active, strict=True)
    ]


def proxy(weights: Sequence[float], allocation: Sequence[int]) -> float:
    return max((w * a for w, a in zip(weights, allocation, strict=True)), default=0.0)


def proxy_ceiling(weights: Sequence[float], allocation: Sequence[int]) -> float:
    value = max(
        (Fraction(w) * a for w, a in zip(weights, allocation, strict=True)),
        default=Fraction(0),
    )
    result = float(value)
    return math.nextafter(result, math.inf) if Fraction(result) < value else result


def outward_interval(center: Fraction, radius: float) -> tuple[float, float]:
    lo, hi = center - Fraction(radius), center + Fraction(radius)
    left, right = float(lo), float(hi)
    if Fraction(left) > lo:
        left = math.nextafter(left, -math.inf)
    if Fraction(right) < hi:
        right = math.nextafter(right, math.inf)
    return left, right


def quota_schedule(
    quotas: Sequence[int], caps: Sequence[int], batch: int
) -> Iterator[list[int]]:
    """Dyadic quota buckets, with per-round exploration at most the batch and caps."""
    groups: dict[int, list[int]] = {}
    for i, q in enumerate(quotas):
        if q:
            if q < 0 or caps[i] < 1:
                raise ValueError("Positive quotas require positive capacities")
            groups.setdefault(q.bit_length() - 1, []).append(i)
    for exponent, workers in sorted(groups.items()):
        q = 1 << exponent
        m = len(workers)
        d = min(min(caps[i] for i in workers), 2 * q, max(1, batch // m))
        chunk_size = batch // d
        for start in range(0, 2 * q, d):
            amount = min(d, 2 * q - start)
            for offset in range(0, m, chunk_size):
                allocation = [0] * len(quotas)
                for i in workers[offset : offset + chunk_size]:
                    allocation[i] = amount
                yield allocation


@dataclass(frozen=True)
class Public:
    workers: int
    batch: int
    horizon: int
    sigma: float

    def __post_init__(self) -> None:
        if min(self.workers, self.batch, self.horizon) < 1:
            raise ValueError("Workers, batch, and horizon must be positive")
        if not math.isfinite(self.sigma) or self.sigma < 0:
            raise ValueError("Sigma must be finite and nonnegative")


class ParallelTaskAllocation:
    """Frozen-phase, quota-bucket policy with nested confidence intervals."""

    def __init__(self, config: Public):
        self.config = config
        n, B, K, sigma = (config.workers, config.batch, config.horizon, config.sigma)
        sigma_bar = max(1.0, sigma)
        self.t = math.log(64 * n * B * B * K**3 * (1 + sigma_bar))
        self.clip = 1 + sigma_bar * math.sqrt(2 * self.t)
        self.chi = self.clip * self.t
        self.bias = (1 + sigma_bar) * math.exp(-self.t)
        self.epsilon = math.sqrt((B / n + n / B) / K)
        self.lower = [0.0] * n
        self.upper = [1.0] * n
        self.counts = [0] * n
        self.raw_sum = [Fraction(0)] * n
        self.clipped_sum = [Fraction(0)] * n
        self.active = [True] * n
        self.theta = float(B)
        self.rounds = 0
        self.phase_start = 0
        self.phases: list[dict] = []
        self.eliminations: list[dict] = []
        self.failed_intervals = False
        self.failed_quota_completion = False
        self._schedule: Iterator[list[int]] | None = None
        self._phase_upper = self.upper.copy()
        self._phase_caps = [B] * n
        self._last: list[int] | None = None

    def _geometry(self) -> tuple[float, list[int], list[float], list[int]]:
        B = self.config.batch
        optimal = ras(self.upper, B, [B if x else 0 for x in self.active])
        L = proxy_ceiling(self.upper, optimal)
        caps = capacities(self.lower, L, B, self.active)
        D = [c * (u - s) for c, u, s in zip(caps, self.upper, self.lower, strict=True)]
        return L, caps, D, optimal

    def _start_phase(self) -> None:
        L, caps, D, _ = self._geometry()
        for i, s in enumerate(self.lower):
            if self.active[i] and s > L:
                self.active[i] = False
                self.eliminations.append({"worker": i, "iteration": self.rounds + 1})
        L, caps, D, _ = self._geometry()
        while self.theta > self.epsilon and max(D) <= self.theta / 2:
            self.theta /= 2
        self._phase_upper = self.upper.copy()
        self._phase_caps = caps
        self.phase_start = self.rounds
        if self.theta <= self.epsilon or L <= self.epsilon:
            self._schedule = None
            return
        quotas = [
            math.ceil(
                256 * self.chi * u * c * c / self.theta**2
                + 32 * self.chi * c / self.theta
            )
            + 1
            if c
            else 0
            for u, c in zip(self.upper, caps, strict=True)
        ]
        self._schedule = quota_schedule(quotas, caps, self.config.batch)

    def choose(self) -> list[int]:
        if self._last is not None:
            raise RuntimeError("Feedback must be supplied before choosing again")
        if self.rounds >= self.config.horizon:
            raise RuntimeError("Horizon exhausted")
        n, B = self.config.workers, self.config.batch
        if self.failed_intervals or self.failed_quota_completion:
            result = [B // n + (i < B % n) for i in range(n)]
        else:
            if self._schedule is None:
                self._start_phase()
            if self._schedule is None:
                result = self._geometry()[3]
            else:
                try:
                    explore = next(self._schedule)
                except StopIteration:
                    self.failed_quota_completion = True
                    return self.choose()
                residual = ras(
                    self._phase_upper,
                    B - sum(explore),
                    [c - e for c, e in zip(self._phase_caps, explore, strict=True)],
                )
                result = [e + r for e, r in zip(explore, residual, strict=True)]
                assert all(
                    a <= c for a, c in zip(result, self._phase_caps, strict=True)
                )
        assert sum(result) == B and all(isinstance(a, int) and a >= 0 for a in result)
        self._last = result
        return result.copy()

    def observe(self, feedback: Sequence[Sequence[float]]) -> None:
        if self._last is None or len(feedback) != self.config.workers:
            raise RuntimeError("Feedback does not match an outstanding action")
        if any(len(row) != a for row, a in zip(feedback, self._last, strict=True)):
            raise ValueError("Exactly the assigned observations must be supplied")
        if any(not math.isfinite(x) or x <= 0 for row in feedback for x in row):
            raise ValueError("The model requires strictly positive finite times")
        for i, values in enumerate(feedback):
            self.counts[i] += len(values)
            self.raw_sum[i] += sum((Fraction(x) for x in values), Fraction(0))
            self.clipped_sum[i] += sum(
                (Fraction(min(x, self.clip)) for x in values), Fraction(0)
            )
            N = self.counts[i]
            if N and self.active[i]:
                r = 2 * math.sqrt(self._phase_upper[i] * self.chi / N)
                r += 2 * self.chi / N + self.bias
                rg = self.config.sigma * math.sqrt(2 * self.t / N)
                clipped_lo, clipped_hi = outward_interval(self.clipped_sum[i] / N, r)
                raw_lo, raw_hi = outward_interval(self.raw_sum[i] / N, rg)
                self.lower[i] = max(self.lower[i], clipped_lo, raw_lo, 0.0)
                self.upper[i] = min(self.upper[i], clipped_hi, raw_hi, 1.0)
                if self.lower[i] > self.upper[i]:
                    self.failed_intervals = True
        self.rounds += 1
        self._last = None
        if not self.failed_intervals and self._schedule is not None:
            _, _, D, _ = self._geometry()
            if max(D) <= self.theta / 2:
                self.phases.append(
                    {
                        "theta": self.theta,
                        "start": self.phase_start + 1,
                        "end": self.rounds,
                        "finished": True,
                    }
                )
                self.theta /= 2
                self._schedule = None

    def report(self) -> dict:
        phases = self.phases.copy()
        if self._schedule is not None:
            phases.append(
                {
                    "theta": self.theta,
                    "start": self.phase_start + 1,
                    "end": self.rounds,
                    "finished": False,
                }
            )
        return {
            "iterations": self.rounds,
            "samples": sum(self.counts),
            "warmup_iterations": 0,
            "warmup_samples": 0,
            "warmup_regret": 0.0,
            "requires_positive_lower_warmup": False,
            "phases": phases,
            "eliminations": self.eliminations,
            "failed_intervals": self.failed_intervals,
            "failed_quota_completion": self.failed_quota_completion,
            "formal_regret_certified": False,
        }
