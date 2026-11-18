# Novelty assessment: CorruptedFirstOrderDescent

[`result`](../../LongTails/Theorems/CorruptedFirstOrderDescent.lean) proves the following. Let f be L-smooth on ℝ^d with f(x₀) − inf f ≤ Δ. Each call returns a value–gradient pair. A clean reply has its value within ε²/(128L) of f(x), and its vector equals g(x) for a fixed map g with ‖g − ∇f‖ ≤ ε/8. An adaptive adversary may replace up to k replies along any history with arbitrary, unbounded pairs. On every seed and every fault pattern, the [constructed algorithm](../../LongTails/Algorithms/CorruptedFirstOrderDescent.lean) returns a point with ‖∇f‖ ≤ ε ([setup](../../LongTails/Setups/CorruptedFirstOrderNonconvex.lean)).

**Complexity.** The proved budget is ⌈16LΔ/ε²⌉ + 5k + 4 joint calls, that is,

  N = O(1 + k + LΔ/ε²).

Here L is the gradient-Lipschitz constant, Δ the initial gap, ε the target gradient norm and k the corruption budget. The bound holds for any d ≥ 0, L, ε > 0, Δ ≥ 0 and k ≥ 0. The updates use k, L and ε; Δ enters only through the budget.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| GD with step 1/L (Nesterov, *Lectures on Convex Optimization*, 2018, §1.2.3), with each query repeated 2k+1 times and majority gradient taken (reduction derived here) | O((k+1)(1 + LΔ/ε²)) → O(1 + k + LΔ/ε²) | Speedup Θ(min{k+1, 1+LΔ/ε²}). Example: k ≍ LΔ/ε² gives (LΔ/ε²)² → LΔ/ε². None at k = 0 (same order). | None: same instance class | None: both are deterministic guarantees on the returned point and both need k | This result also needs values accurate to ε²/(128L) on clean calls; the replicated GD needs no values at all |
| Scheinberg–Xie, arXiv:2511.19411v1 (Nov 2025, prior), Thms 1–3 and Assumption 3 | Not comparable → O(1 + k + LΔ/ε²) | Not comparable: their bounds concern a high-probability hitting time | Incomparable. Theirs: each gradient is corrupted with probability δ₁ < 1/2 per iteration, and value corruption is bounded (CZO: \|error\| ≤ ε_f + ε_c almost surely). Here: a deterministic count of ≤ k corruptions, which may come in a burst and be unbounded | Theirs: hitting time, high probability. Here: returned point, every seed | Theirs allows stochastic clean gradients; here the clean gradient must be a fixed map |
| Paes Leme–Podimata–Schneider, arXiv:2206.07528v3 (COLT 2022), Thm 3.1 | Regret O(C + dLD log(T/L)) on convex functions → not comparable | Not comparable: they bound regret for convex problems on a compact domain | Incomparable. Theirs: convex G-Lipschitz f on a compact domain, with total corruption magnitude C and bounded replies. Here: nonconvex smooth f, a count-bounded corruption budget and unbounded replies | Their method does not need C (agnostic); here k must be known | Shows that an additive corruption cost is already known for cutting-plane-style convex feedback |

**Reductions and ancestry.** Batching or majority voting gives only the multiplicative bound in row 1. Adaptive majority still costs about k+1 calls per point when the adversary does nothing. Scheinberg–Xie's framework fails because one unbounded false value breaks their Assumption 3 descent charge. The new step combines three pieces: descent tests at absolute thresholds a − jh, anchored by a median of 2k+1 values; a backtracking stack; and votes that cancel each other at the current point. A ±1 potential shows that each clean call gains one unit and each fault costs at most one. I read the proof structure and invariants (`Proofs/CorruptedFirstOrderExecution.lean`, `…Progress.lean`) but did not run a build or axiom audit. The lie-counting idea goes back to the Rényi–Ulam search literature (Rivest et al. 1980; Pelc's survey). It is proof ancestry, not a competing bound. The paired [lower bound](../../LongTails/Theorems/CorruptedFirstOrderLowerBound.lean), from the same commit, shows that Ω(k + LΔ/ε²) calls are necessary when LΔ/ε² ≥ 2²⁶ and d is large. It extends Carmon et al. (arXiv:1710.11606, Thm 2) with a k-reply delay.

**Search coverage (2026-11-18).** I searched arXiv and the web for corrupted, lying and Byzantine first-order oracles, step-search methods with unreliable oracles, total-budget adversarial subgradients (Gösgens–Van Parys 2025, whose budget limits magnitude in the convex setting), and fault-tolerant query complexity. I did not read Kenyon–Yao (FOCS 1989) or the Maharjan–Watson text in full. The companion note's citations match the sources I checked. The result was introduced in commit 5b11e6b5 (2026-11-18).

**Conclusion**

**Yes: under a count-bounded, arbitrary-corruption first-order oracle, the proved cost of handling corruptions becomes additive rather than multiplicative.** The strongest baseline that applies end to end is ordinary gradient descent with every query repeated 2k+1 times:

| | calls to reach ‖∇f‖ ≤ ε |
|---|---|
| repeated GD | O((k+1)(1 + LΔ/ε²)) |
| this result | O(1 + k + LΔ/ε²) |

The gain is a factor of Θ(min{k+1, 1+LΔ/ε²}), which is polynomial when k and LΔ/ε² are of the same order. In the large-dimension regime, the paired lower bound shows the new bound is tight up to constants. At k = 0 the result only matches plain GD.

The price is a stronger clean oracle. Clean values must be accurate to ε²/(128L), clean gradients must be repeatable (a fixed map), and k must be known. Published corruption-robust analyses either assume per-iteration probabilistic corruption with bounded value errors or study convex regret, so neither gives a competing bound here.

The comparison establishes the gain only over a constructed reduction, not over a published algorithm for this model. The literature search found no prior additive guarantee, but the fault-tolerant decision-tree literature was not fully checked, so priority is not certain. What can be claimed is a new deterministic Θ(k + LΔ/ε²) stationarity complexity for smooth nonconvex optimization with k arbitrary faulty value–gradient replies.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
