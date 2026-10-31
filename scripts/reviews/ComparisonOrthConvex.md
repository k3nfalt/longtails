# ComparisonOrthConvex: accelerated smooth convex minimization from exact pairwise comparisons

[`result`](../../LongTails/Theorems/ComparisonOrthConvex.lean) proves the following. Let f : ℝⁿ → ℝ be convex and differentiable with an L-Lipschitz gradient, and let some minimizer satisfy ‖x₀ − x⋆‖ ≤ R ([setup](../../LongTails/Setups/ComparisonSmoothConvex.lean)). The only oracle returns the bit 1[f(x) ≤ f(y)]. The deterministic method [`comparisonOrth`](../../LongTails/Algorithms/ComparisonOrth.lean), which knows n, L, R, ε and x₀, returns a last iterate x_K with f(x_K) − f(x⋆) ≤ ε within the budget below.

**Complexity.** The proved budget is (⌈6√(LR²/ε)⌉+1)·M·(3n+7M²), with M = 12·log₂(n⌈LR²/ε⌉)+96. In simplified form, this is

  N = O( (1 + √(LR²/ε)) · ( n·log(2n(1+LR²/ε)) + log³(2n(1+LR²/ε)) ) ) comparisons.

Here n is the dimension, L the gradient-Lipschitz constant, R the initial distance bound and ε the objective accuracy. Each iteration spends n(M+2) comparisons on direction estimation, 4M³+6M²+3M on a nested ternary search over a 3-D box, and one on a keep-if-better check. All of these are counted.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhang–Li, Comparison-AdaNGD, [arXiv:2405.11454v1](https://arxiv.org/abs/2405.11454v1), Thm 2 (May 2024; later versions retitled) | O(n·(LR²/ε)·log(n·LR²/ε)) → N | Gain of a factor of about √(LR²/ε) for LR²/ε ≥ 1 (when n ≥ log²(n·LR²/ε)) | None. Same class, oracle and criterion. | Best of the iterates (chosen by comparisons) → last iterate. Both are deterministic. | Adds an additive √(LR²/ε)·log³ term to every iteration's cost. Same known parameters. |
| Zhang–Li, comparison cutting plane, same paper, Thm 3 | O(n²·log(n·LR²/ε)) → N | Better by a factor of about n/√(LR²/ε) when LR²/ε < n² (up to logs). Example: at LR²/ε = n, the bound improves from Õ(n²) to Õ(n^1.5). | None | None | **Worse** by a factor of about √(LR²/ε)/n when LR²/ε > n². The cutting-plane method also depends on ε only logarithmically. |
| Lobanov–Gasnikov–Krasnov, OrderACDM, [arXiv:2402.09014v3](https://arxiv.org/abs/2402.09014) (NeurIPS 2024), Thm 4.1. **Applies only when μ > 0.** | For μ-strongly convex f, uniform sampling: Õ(n√(L/μ)·log(1/ε)) in expectation. There is no bound for μ = 0. → N | Not comparable when μ = 0. When μ > 0, the selected result is worse: it has no linear rate. | Strong convexity μ > 0 → merely convex. The proof in their App. E divides by μ (step ①), so it does not extend to μ = 0. | Expected accuracy → deterministic | Their bound depends on the coordinate constants L_i, which can beat n√L on anisotropic instances. This result does not. |
| Wu et al., [arXiv:2609.18230](https://arxiv.org/abs/2609.18230) (Sep 2026, before this result). **Uses a stronger oracle.** | Exact *values*, queries restricted to a ball: O(n√(LR²/ε)) → N | None: same order up to logs | Value oracle → comparison-only oracle. A comparison cannot reveal values, so their method cannot be run here. | None | Adds log factors. Their finite-difference method needs magnitudes. |

**Lower bound.** Dorn et al., [arXiv:2610.00345](https://arxiv.org/abs/2610.00345) (29 Sep 2026), Thm 2.1, proves Ω(n·min{n, √(LR²/ε)}) exact-value queries for randomized algorithms when ε ≤ LR²/32. One comparison can be simulated by two value queries, so the same bound holds for comparison algorithms. Together with Zhang–Li Thm 3, this result therefore pins down the comparison complexity as n·min{n, √(LR²/ε)} up to logarithmic factors.

**Reduction check and mechanism.** I checked the standard routes, and none of them reproduces the bound:

- **Regularization plus OrderACDM fails.** A comparison of f does not give a comparison of f + (μ/2)‖x−x₀‖².
- **AGD, OGM-LS ([Drori–Taylor, arXiv:1803.05676](https://arxiv.org/abs/1803.05676) §4.2) and SESOP/ORTH fail.** They all combine *unnormalized* gradients with fixed weights. Comparisons are invariant under f ↦ c·f, so gradient magnitudes cannot be identified.
- **Random pursuit fails.** Stich's accelerated variant (arXiv:1406.2010) has no convergence proof.

The new mechanism is a Nemirovski-style orth-method that adds *normalized, orthogonalized* direction estimates with unit weights. Each step does a 3-D box search, and the proof bounds the progress with a power-mean inequality. The robust analysis absorbs direction-estimation and search errors at a cost of only logarithmic factors.

On proof ancestry: Nemirovski's orth-method and SESOP supply the subspace structure; Zhang–Li supply direction estimation. The unit-weight potential argument and the error-robust analysis are additional work. I could not access Nemirovski (1982), so I cannot rule out that it already uses normalized weights. That would affect the novelty of the mechanism, not of the comparison bound.

**Search coverage (30 Oct 2026).** I searched arXiv and the web for comparison, order, dueling and ranking oracles with acceleration, read the theorem statements cited above, and checked the Lobanov–Gasnikov comparison-oracle survey (Doklady 2025/26, abstract only). I found no prior or later accelerated comparison bound for merely convex f. The companion note's citations check out. It omits the Wu et al. value-oracle upper bound. Nemirovski (1982) and the full text of the survey were not accessible.

**Conclusion**

**Yes: with exact comparisons, the result improves the proved complexity for merely convex smooth f whenever LR²/ε < n².**

The strongest earlier guarantees are both from Zhang–Li (2024). Writing T = LR²/ε:

| | Comparisons |
|---|---|
| Best previous (Zhang–Li Thm 2 / Thm 3) | Õ(min{n·T, n²}) |
| This result | Õ(n·√T) (+ √T·log³ per-iteration overhead) |

For 1 < T < n², this gains a factor of min{√T, n/√T}. For example, at T = n the bound improves from Õ(n²) to Õ(n^1.5). The result is worse than cutting planes when T > n². The only accelerated comparison method (Lobanov et al.) requires strong convexity, and its proof breaks at μ = 0.

The exact-value lower bound Ω(n·min{n, √T}) transfers to comparisons. The new bound is therefore optimal up to logarithms in its regime, and comparisons match value queries there. The obvious reductions are blocked because comparisons cannot reveal gradient magnitudes. The contribution that can be claimed is the first accelerated comparison complexity for convex functions without strong convexity, which together with cutting planes gives near-tight comparison complexity. Two things remain unconfirmed: a possibly normalized variant in Nemirovski (1982), and any unindexed concurrent work.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
