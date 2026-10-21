import importlib.util
import itertools
import random
import sys
import unittest
from pathlib import Path

MODULE = (
    Path(__file__).resolve().parents[1]
    / "LongTailsOnline/Algorithms/ParallelTaskAllocation.py"
)
SPEC = importlib.util.spec_from_file_location("parallel_task_allocation", MODULE)
ata = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ata
SPEC.loader.exec_module(ata)


def allocations(n, B):
    if n == 1:
        yield [B]
    else:
        for first in range(B + 1):
            for tail in allocations(n - 1, B - first):
                yield [first] + tail


class ParallelTaskAllocationTests(unittest.TestCase):
    def test_ras_against_exhaustive_integer_minimum(self):
        rng = random.Random(4901)
        for n, B in itertools.product(range(1, 5), range(7)):
            feasible = list(allocations(n, B))
            for _ in range(20):
                u = [rng.choice([0.0, 0.125, 0.25, 0.5, 1.0, 3.0]) for _ in range(n)]
                caps = [rng.randrange(B + 1) for _ in range(n)]
                if sum(caps) < B:
                    continue
                a = ata.ras(u, B, caps)
                expected = min(
                    ata.proxy(u, b)
                    for b in feasible
                    if all(x <= c for x, c in zip(b, caps))
                )
                self.assertEqual(ata.proxy(u, a), expected)
                self.assertEqual(sum(a), B)
                self.assertTrue(all(x <= c for x, c in zip(a, caps)))

    def test_hint_geometry_and_exact_capacity_filler(self):
        rng = random.Random(302)
        for _ in range(3000):
            n, B = rng.randrange(1, 20), rng.randrange(1, 30)
            s = [rng.choice([0.0, rng.random()]) for _ in range(n)]
            u = [x + rng.random() * (1 - x) for x in s]
            mu = [x + rng.random() * (y - x) for x, y in zip(s, u)]
            b = ata.ras(u, B)
            L = ata.proxy_ceiling(u, b)
            Lminus = ata.proxy(s, ata.ras(s, B))
            Lstar = ata.proxy(mu, ata.ras(mu, B))
            C = ata.capacities(s, L, B)
            D = [c * (y - x) for c, x, y in zip(C, s, u)]
            theta = max(D)
            self.assertLessEqual(Lminus, Lstar + 1e-12)
            self.assertLessEqual(Lstar, L + 1e-12)
            self.assertLessEqual(L - Lminus, theta + 1e-12)
            self.assertLessEqual(ata.proxy(mu, b) - Lstar, theta + 1e-12)
            self.assertTrue(all(x <= c for x, c in zip(b, C)))
            optimal = ata.ras(mu, B)
            self.assertTrue(all(optimal[i] == 0 for i in range(n) if s[i] > L))
            e = [0] * n
            for _ in range(rng.randrange(B + 1)):
                possible = [i for i in range(n) if e[i] < C[i]]
                e[rng.choice(possible)] += 1
            residual = ata.ras(u, B - sum(e), [c - x for c, x in zip(C, e)])
            a = [x + y for x, y in zip(e, residual)]
            self.assertEqual(sum(a), B)
            self.assertTrue(all(x <= c for x, c in zip(a, C)))
            self.assertLessEqual(ata.proxy(u, residual), L + 1e-12)
            self.assertLessEqual(ata.proxy(mu, a) - Lstar, 2 * theta + 1e-12)
            self.assertLessEqual(ata.proxy(mu, a), L + ata.proxy(u, e) + 1e-12)

    def test_bucket_schedule_cost_and_round_bounds(self):
        rng = random.Random(991)
        for _ in range(400):
            n, B = rng.randrange(1, 35), rng.randrange(1, 25)
            C = [rng.randrange(1, B + 1) for _ in range(n)]
            q = [rng.randrange(1, 90) for _ in range(n)]
            u = [rng.random() + 0.001 for _ in range(n)]
            J = len({v.bit_length() for v in q})
            H = max(v / c for v, c in zip(q, C))
            Q = max(v * x for v, x in zip(q, u))
            totals = [0] * n
            rounds, total_load = 0, 0.0
            for e in ata.quota_schedule(q, C, B):
                rounds += 1
                total_load += ata.proxy(u, e)
                self.assertLessEqual(sum(e), B)
                self.assertTrue(all(x <= c for x, c in zip(e, C)))
                totals = [a + b for a, b in zip(totals, e)]
            self.assertTrue(all(v <= count <= 2 * v for v, count in zip(q, totals)))
            self.assertLessEqual(rounds, 4 * sum(q) / B + 2 * J * (H + 1) + 1e-10)
            self.assertLessEqual(total_load, 4 * Q * (J + n / B) + 1e-8)

    def test_harmonic_integer_oracle_geometry(self):
        rng = random.Random(230)
        for _ in range(1500):
            n, B = rng.randrange(1, 50), rng.randrange(1, 50)
            u = [10 ** rng.uniform(-7, 0) for _ in range(n)]
            V = ata.proxy(u, ata.ras(u, B))
            self.assertLessEqual(V * sum(1 / x for x in u), B + n - 1 + 1e-8)

    def test_actual_policy_positive_unbounded_range_and_horizon(self):
        rng = random.Random(401)
        for n, B, sigma in [(7, 2, 2.0), (3, 8, 2.0), (5, 5, 0.0), (1, 4, 0.0)]:
            K = 120
            policy = ata.ParallelTaskAllocation(ata.Public(n, B, K, sigma))
            means = [0.02 + 0.9 * (i + 1) / n for i in range(n)]
            last_lo, last_up = policy.lower.copy(), policy.upper.copy()
            regret = 0.0
            optimum = ata.proxy(means, ata.ras(means, B))
            for t in range(K):
                a = policy.choose()
                if sigma:
                    feedback = [
                        [
                            4.01 if rng.random() < (means[i] - 0.01) / 4 else 0.01
                            for _ in range(a[i])
                        ]
                        for i in range(n)
                    ]
                else:
                    feedback = [[means[i]] * a[i] for i in range(n)]
                policy.observe(feedback)
                regret += ata.proxy(means, a) - optimum
                self.assertEqual(sum(policy.counts), (t + 1) * B)
                self.assertTrue(all(x <= y for x, y in zip(last_lo, policy.lower)))
                self.assertTrue(all(x >= y for x, y in zip(last_up, policy.upper)))
                last_lo, last_up = policy.lower.copy(), policy.upper.copy()
            report = policy.report()
            self.assertEqual(report["samples"], B * K)
            self.assertFalse(report["failed_intervals"])
            self.assertFalse(report["failed_quota_completion"])
            self.assertFalse(report["formal_regret_certified"])
            self.assertGreaterEqual(regret, -1e-10)
            with self.assertRaisesRegex(RuntimeError, "Horizon exhausted"):
                policy.choose()

    def test_incomplete_phase_is_reported(self):
        policy = ata.ParallelTaskAllocation(ata.Public(4, 2, 10, 1.0))
        for _ in range(10):
            a = policy.choose()
            policy.observe([[0.5] * v for v in a])
        self.assertFalse(policy.report()["phases"][-1]["finished"])

    def test_feedback_protocol_rejects_missing_samples(self):
        policy = ata.ParallelTaskAllocation(ata.Public(3, 4, 20, 1.0))
        policy.choose()
        with self.assertRaises(ValueError):
            policy.observe([[], [], []])
        with self.assertRaises(RuntimeError):
            policy.choose()

    def test_safe_capacities_cannot_certify_precision(self):
        s, mu, u = [0.2, 0.0], [0.2, 0.1], [0.2, 1.0]
        B = 1
        action = ata.ras(u, B)
        V = ata.proxy_ceiling(u, action)
        safe = ata.capacities(u, V, B)
        safe_D = [c * (y - x) for c, x, y in zip(safe, s, u)]
        self.assertEqual(safe, [1, 0])
        self.assertEqual(max(safe_D), 0.0)
        self.assertGreater(ata.proxy(mu, action) - ata.proxy(mu, ata.ras(mu, B)), 0.0)
        optimistic = ata.capacities(s, V, B)
        self.assertGreater(max(c * (y - x) for c, x, y in zip(optimistic, s, u)), 0.0)


if __name__ == "__main__":
    unittest.main()
