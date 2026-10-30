# Accelerated smooth convex optimization from pairwise comparisons: Õ(n·√(LR²/ε)) comparisons

**Lean files.**
- Main theorem: [`ComparisonOrthConvex.lean`](ComparisonOrthConvex.lean), which contains `OracleTemplate.ComparisonOrth.result` and the public budget `OracleTemplate.ComparisonOrth.budget`.
- Setup: [`../Setups/ComparisonSmoothConvex.lean`](../Setups/ComparisonSmoothConvex.lean).
- Algorithm: [`../Algorithms/ComparisonOrth.lean`](../Algorithms/ComparisonOrth.lean), which defines `comparisonOrth`, the per-iteration plan `orthStepPlan`, the direction estimator `dirPlan` and the nested ternary box search `boxPlan`.
- Proof chain:
  - [`ComparisonTernary`](../Proofs/ComparisonTernary.lean): robust ternary search with inexact inner minimization, and convexity/Lipschitz continuity of partial infima.
  - [`ComparisonDirection`](../Proofs/ComparisonDirection.lean): deterministic gradient-direction estimation from comparisons (`dir_accuracy`).
  - [`ComparisonBox`](../Proofs/ComparisonBox.lean): three-dimensional box minimization from comparisons (`box_guarantee`).
  - [`ComparisonFrame`](../Proofs/ComparisonFrame.lean): orthonormal-or-zero frames and projections.
  - [`ComparisonOrthStep`](../Proofs/ComparisonOrthStep.lean): the one-iteration invariant and progress inequality (`orth_step`).
  - [`ComparisonOrthConvergence`](../Proofs/ComparisonOrthConvergence.lean): the global argument, parameter tuning, oracle-call count and execution (`orth_converges`, `orth_len_le`, `execute_cmp`).

## Problem, oracle, and assumptions

We minimize f : ℝⁿ → ℝ (Lean: `EuclideanSpace ℝ (Fin n)`) under the standard smooth convex assumptions:

- **(A1)** f is convex and differentiable, with L-Lipschitz gradient: ‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖.
- **(A2)** A minimizer x⋆ exists with ‖x₀ − x⋆‖ ≤ R.

Strong convexity is **not** assumed.

**Oracle (the only information channel).** A query is a pair of points (x, y); the reply is the bit 1[f(x) ≤ f(y)]. No function values or gradients are revealed. This is the exact ("order", "dueling", "preference") comparison oracle of Zhang–Li, Lobanov et al. and Wang et al. (references below), motivated by preference feedback, as in RLHF and human-in-the-loop black-box tuning.

**Known to the algorithm:** n, L, R, ε and x₀. These are the same as in the compared non-accelerated comparison methods, which use L and a horizon or step tied to ε.

**Accuracy criterion.** The algorithm is deterministic. Its output is the last iterate x_K, and the guarantee is f(x_K) − f(x⋆) ≤ ε. In Lean this is stated almost surely with respect to the trivial seed measure.

**Cost model.** Every comparison counts as one oracle call. This includes all direction-estimation probes, all comparisons inside the nested searches (including the re-evaluation of the inner search at the final ternary point), and the keep-if-better comparison.

## Algorithm (`comparisonOrth`)

Write T = LR²/ε, K = ⌈6√T⌉ + 1, m = 12·(log₂(n⌈T⌉) + 8), and h = R/(160 n² K T²).

The state is (x_k, d_k, u₁, u₂, u₃), where (u₁, u₂, u₃) is an orthonormal-or-zero frame spanning S_{k−1} ⊇ {x_k − x₀, d_{k−1}}. Initially x = x₀, d = 0 and all u's are 0. For k = 0, …, K−1:

1. **Direction estimation (`dirPlan`, n(m+2) comparisons).** Probe T(z) = 1[f(x−hz) ≤ f(x+hz)]. First compute coordinate signs s_i = T(e_i). Then run a single-pass tournament with tests T(s_i e_i − s_c e_c) to find a pivot coordinate c with large |∂_c f|. Finally, for every i, run m bisection steps on t ∈ [−2, 2] with test T(s_c(e_i − t e_c)), which estimates the ratio ∂_i f/∂_c f. The output ĝ is a unit vector with ‖ĝ − ∇f/‖∇f‖‖ ≤ 2√n(2^{1−m} + 9Lh√n/(2‖∇f‖)) whenever 2(n+1)Lh√n ≤ ‖∇f(x)‖ (`dir_accuracy`).
2. **Orthogonalized normalized direction.** Set Ĝ_k = (ĝ − P_{S_{k−1}}ĝ)/‖·‖ (0 if the vector is 0) and d_k = d_{k−1} + Ĝ_k.
3. **New frame.** u₁' = (x_k − x₀)/‖x_k − x₀‖, u₂' = normalized(d_{k−1} − ⟨d_{k−1}, u₁'⟩u₁'), u₃' = Ĝ_k.
4. **Box search (`boxPlan`, 4m³ + 6m² + 3m comparisons).** Approximately minimize f(x₀ + a u₁' + b u₂' + c u₃') over the box |a| ≤ max(R, ‖x_k − x₀‖), |b|, |c| ≤ R. The search is a three-level nested ternary search with m rounds per level.
5. **Keep-if-better (1 comparison).** x_{k+1} is the better of the box output and x_k.

The output is x_K.

## Guarantee (`result`)

Under (A1)–(A2), for every n ≥ 1, L, R, ε > 0, the algorithm returns x_K with f(x_K) − f(x⋆) ≤ ε. It uses at most

  budget = (⌈6√(LR²/ε)⌉ + 1) · m · (3n + 7m²),  with m = 12·log₂(n⌈LR²/ε⌉) + 96,

comparisons. That is Õ(n·√(LR²/ε)) comparisons, with an additive polylog³ term per iteration.

## What is new, and the mechanism

**Closest prior results (comparison oracle, smooth convex, no strong convexity).**
- Zhang–Li, "Comparisons are all you need for optimizing smooth functions", [arXiv:2405.11454v1](https://arxiv.org/abs/2405.11454v1) (May 2024), convex results: Õ(n/ε) comparisons, i.e. Õ(n·LR²/ε) (normalized gradient descent with comparison-estimated directions), and Õ(n²) by a cutting-plane method. Versions v2/v3 were retitled "Gradient Testing and Estimation by Comparisons" and focus on direction estimation (O(n log(1/δ)) comparisons, optimal).
- Lobanov, Gasnikov, Krasnov, "Acceleration Exists! Optimization Problems When Oracle Can Only Compare Objective Function Values", [arXiv:2402.09014v3](https://arxiv.org/abs/2402.09014). Thm 3.2 (OrderRCD, convex) is non-accelerated: Õ(S_α R²/ε). Thm 4.1 (OrderACDM) is accelerated **only for μ-strongly convex f**: Õ(S_{α/2}/√μ · log(1/ε)). Its proof (App. E) uses μ > 0 in an essential way.
- Wang, Zhang, Tao, Zhang, Li, "Finding Stationary Points by Comparisons", ICML 2026 (PMLR v306, [arXiv:2606.27082](https://arxiv.org/abs/2606.27082)), treats the nonconvex case; its open questions include improving the dependence on n and ε of comparison methods (stated there for the nonconvex setting).

To our knowledge (citation screens of 2402.09014 and 2405.11454 in Oct 2026; see the limitations below), no accelerated comparison-oracle rate for smooth convex f **without strong convexity** was known. Our bound Õ(n√(LR²/ε)) improves Õ(n·LR²/ε) polynomially for every accuracy. It improves the Õ(n²) cutting-plane bound when √(LR²/ε) < n.

**Why the standard reductions do not apply.**
1. *Regularize and use the strongly convex accelerated method.* A comparison of f does not yield a comparison of f + (μ/2)‖x − x₀‖², because comparison information is not additive. So Lobanov et al.'s Thm 4.1 cannot be applied to a regularized objective.
2. *Estimate ∇f and run AGD.* Comparisons are invariant under f ↦ φ∘f for increasing φ. In particular f and c·f (0 < c ≤ 1) give identical answers and are both in the class, so ‖∇f‖ is unidentifiable. Estimate-sequence and AGD updates such as v ← v − a∇f need the magnitude. Nemirovski-type subspace methods have the same problem: SESOP / the orth-method, as described in [arXiv:1710.00797](https://arxiv.org/abs/1710.00797) §3 and in Drori–Taylor's references, use f-independent weights on **unnormalized** gradients, ω_k∇f(x_k).
3. *Full-span greedy subspace search* (Drori–Taylor, [arXiv:1803.05676](https://arxiv.org/abs/1803.05676)) is scale-invariant. But it needs k-dimensional minimization at step k. Implemented with comparisons via k-dimensional cutting planes, it costs about Õ(nK + K³) with K = √(LR²/ε). This construction is not in the literature; it was pointed out during review. It matches our bound for K ≤ √n. For √n < K < n our bound is better by a factor up to n^{1/3}, relative to the best of this construction and the n² cutting-plane bound.

**New mechanism: a normalized, orthogonalized 3-D orth-method in a box.**
- The method uses only directions: unit weights on normalized, orthogonalized gradient directions Ĝ_k, plus low-dimensional minimizations. Both are implementable from comparisons.
- The exact argument (`orth_step` + `orth_converges`) runs as follows:
  - (i) A variational inequality at x_k is tested against the box point x₀ + P_{S_{k−1}}(x⋆ − x₀). This gives δ_k ≤ ‖G_k‖·r_k, with G_k = P_⊥∇f(x_k) and r_k = ⟨Ĝ_k, x₀ − x⋆⟩.
  - (ii) Since Ĝ_k ⊥ d_{k−1}, we have ‖d_K‖² ≤ K, so Σr_k ≤ √K·R.
  - (iii) A step along −Ĝ_k stays in the box and gives δ_{k+1} ≤ δ_k − c‖G_k‖²/L.
  - (iv) Hence 1/δ_{k+1} ≥ 1/δ_k + 1/(8Lρ_k²). A power-mean (tangent-line) inequality Σ1/ρ_k² ≥ K³/(Σρ_k)² then gives δ_K ≤ 18LR²/K².
- The box (|a| ≤ max(R, ‖x_k − x₀‖), |b|, |c| ≤ R) keeps ‖x_k − x₀‖² ≤ (2k+1)R². It also makes all search errors polynomially small in log scale.
- The robust analysis handles inexact directions. These are amplified by ‖∇f‖/‖G_k‖ ≤ 4T/3 at the box boundary, and this costs only a log factor. It also handles inexact box minimization, via an approximate variational inequality from η-optimality, and degenerate frames.

**Near-optimality (not part of the theorem).** One comparison can be simulated by two exact value queries. So the value-query lower bound Ω(n·min{n, √(LR²/ε)}) of [arXiv:2610.00345v1](https://arxiv.org/abs/2610.00345) (adaptive randomized algorithms, quadratics) also holds for comparisons. Together with the Õ(n²) cutting-plane bound, our result gives comparison complexity n·min{n, √(LR²/ε)} up to logarithmic factors.

## Limitations and honest comparisons

- **Exact comparisons only.** Noisy or Bradley–Terry comparisons and bounded-noise order oracles are not covered.
- **Worst-case, not coordinate-adaptive.** For strongly convex f, Lobanov et al.'s coordinate bound Σ√L_i/√μ can beat n√(L/μ) on anisotropic instances. A coordinate-adaptive convex bound Σ√L_i·R/√ε remains open. We do not claim a strongly convex corollary.
- The algorithm needs L, R and ε. It is not parameter-free.
- Constants are large, and the budget contains a log³(n·LR²/ε) term per iteration, in addition to the n·log term.
- The method itself (normalized, unit-weight, orthogonalized orth-method) is, to our knowledge, new. Its closest relatives are SESOP and Nemirovski's orth-method, which use weighted unnormalized gradients. We could not access Nemirovski's 1982 paper (Izvestia AN SSSR 2:937–947), so this novelty claim is subject to that check. The comparison-complexity result does not depend on it.
- Literature screen: citation lists of 2402.09014 and 2405.11454 (Semantic Scholar, Oct 2026), arXiv queries on comparison/order/dueling oracles, ICML 2026 proceedings, and recent math.OC/cs.LG preprints. Related work that does not give accelerated convex comparison rates includes Saha–Koren–Mansour (dueling convex optimization), Karabag et al. (ellipsoid with comparisons), Scheinberg–Xiong (arXiv:2604.26867, function-free, Õ(dD²/ε²)) and noisy-comparison papers (2602.05622, 2601.21166).
