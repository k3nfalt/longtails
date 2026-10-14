# Novelty assessment: damped accelerated method under relative gradient error (convex)

[`result`](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean) proves the following. Take a convex, L-smooth `f` on a real Hilbert space with a minimizer `x*`, where `‖x₀−x*‖ ≤ R`. Suppose every oracle reply satisfies `‖g−∇f(x)‖ ≤ α‖∇f(x)‖` with `0 ≤ α < 1`; replies may vary with the call index and seed. Then the last iterate `x_N` of the [damped linear-coupling method](../../LongTails/Algorithms/DampedAccelerated.lean), with z-step damping `q = (1−α)/(8+2α²N)`, satisfies `f(x_N)−f(x*) ≤ ε` for every seed. The budget is `N = ⌈7√(LR²/((1−α)ε)) + 11α²LR²/((1−α)ε)⌉` calls ([setup](../../LongTails/Setups/RelativeErrorSmoothConvex.lean)).

**Complexity** (L: smoothness constant; R: initial distance; ε: target accuracy; α: relative error):

  N = O( 1 + √(LR²/((1−α)ε)) + α²LR²/((1−α)ε) ),  valid for every 0 ≤ α < 1.

The algorithm uses L, α, and the ratio LR²/ε (through N). There is no logarithm and no restart. At α = 0 this is the order of Nesterov's method. The exact oracle is admissible, so the `Ω(√(LR²/ε))` exact-gradient lower bound applies in high dimension. Hence the bound is order-optimal, apart from the factor `(1−α)^{-1/2}`, whenever α ≲ (ε/LR²)^{1/4}.

Below, T = LR²/ε.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vasin–Gasnikov, [arXiv:2603.12376](https://arxiv.org/abs/2603.12376) v1 (Mar 2026 preprint), Thm 7.2/F.3: RE-AGM applied to the regularized function `f + (μ/2)‖x−x₀‖²`. Choosing the smallest admissible β with α ≤ (1/3)(12T)^{-β} | O((√T + αT)·log T), only for α ≤ 1/3 and ε < LR² → O(√T + α²T) | The log T factor disappears in every regime. For T^{-1/2} ≤ α ≤ 1/3 the speedup is about min(α√T, 1/α)·log T. Example: α = T^{-1/4} gives T^{3/4}log T → √T. | α ≤ 1/3 → every α < 1 | None: both give the last iterate and need α, L, and LR²/ε | The constant (1−α)^{-1} grows as α → 1. None otherwise. |
| Vasin–Gasnikov, same preprint, Thm 7.1: regularized gradient descent | 12(1+α)²(1−α)^{-6}·T·ln(2T) → O(√T/(1−α)^{1/2} + α²T/(1−α)) | For every α < 1/2 the gain is at least a factor of order log T/α² (at least log T). For α ≤ T^{-1/4} the gain is of order √T·log T. | α < 1/2 → α < 1 | None | None |
| Kornilov et al., [arXiv:2310.00506](https://arxiv.org/abs/2310.00506) v1 (2023; JOTA 2025 version not checked), Thm 3.1: ISTM with p = 2 and damping a | O(LR²·max{N⁻², √α N^{-3/2}, αN⁻¹, α²}). This reaches ε only when α ≲ T^{-1/2}, then with O(√T) calls → same order there | None (same order) where Kornilov applies. Beyond α ≈ T^{-1/2}, Kornilov stalls at the accuracy floor α²LR² and gives no ε-guarantee. | α ≲ (ε/LR²)^{1/2} → any α < 1. The accelerated rate now holds up to α ≲ (ε/LR²)^{1/4}. | None (Kornilov's damping a also depends on N) | None |

**Reduction check.** I found no standard reduction that gives this bound.
- Regularization (as in Vasin–Gasnikov) adds a logarithm, keeps the linear-in-α term αT, and requires α ≤ 1/3.
- Restarts require strong convexity.
- The repository's [strongly convex theorem](../../LongTails/Theorems/AcceleratedInexactStronglyConvex.lean) handles only relative error. Regularizing `f` turns part of that error into an absolute error, which the theorem does not cover.

The new mechanism is the gradient step `x_{k+1} = y_k − g_k/L`. Its descent slack absorbs the error term `αGD`, and the potential is allowed to grow by `1 + 2qα²/(1−α)` per step, with q chosen so that the total growth is at most e. That explains α² instead of α. Proof ancestry: linear coupling and Nesterov's estimate sequences supply the potential. Kornilov et al. (Alg. 1) already damp the z-step. Their analysis, however, has no gradient step, so it bounds ‖z_k−x*‖ by induction, which produces the accuracy floor.

**Search coverage.** Searched on 2026-10-07: arXiv; the PMLR ICML 2024 paper by Hallak–Levy; Vernimmen–Glineur [2506.09730](https://arxiv.org/abs/2506.09730) and [2506.17145](https://arxiv.org/abs/2506.17145); Vasin et al. (OMS 2023). Not comparable:
- Hallak–Levy: constrained problems, with either an accuracy floor 2εMR (Thm 5.4) or a multiplicative criterion θf* (Thm 6.4).
- Vernimmen–Glineur: gradient-norm bounds measured from f(x₀)−f* for gradient descent, and PEP numerics for accelerated methods.

Not accessed: the JOTA text of Kornilov et al., OpenReview, and 2026 proceedings. The result was introduced in commit 84eee5f on 2026-10-03; no later work was found. The companion note's reading of the Vasin–Gasnikov and Kornilov bounds matches the theorems. Its separate two-level proposition is a hand proof outside the Lean result, and I did not verify it. The same goes for its claim that the lower bound in Vasin–Gasnikov Thm 10.2 (order α²T) is invalid. If that lower bound were valid, the α² term here would be order-optimal; this is unresolved.

## Conclusion

**Yes. For moderate relative error, the proved total complexity is polynomially better than the best prior bound I found, and it holds for every α < 1.**

The strongest baseline is the regularized accelerated method of Vasin–Gasnikov (2026 preprint, Thm 7.2), under the same class, oracle, information, and last-iterate criterion:

| | calls for f(x_N) − f* ≤ ε | range |
|---|---|---|
| Vasin–Gasnikov | O((√T + αT)·log T) | α ≤ 1/3 |
| this result | O(√T/(1−α)^{1/2} + α²T/(1−α)) | α < 1 |

The gain is at least a log T factor everywhere. It becomes polynomial for T^{-1/2} ≤ α ≤ 1/3; at α = T^{-1/4}, for example, the cost drops from T^{3/4}log T to √T. The accelerated, optimal-order rate now holds up to α ≈ T^{-1/4}, compared with T^{-1/2} in Kornilov et al. The cost is a constant (1−α)^{-1} as α → 1, a regime where no prior distance-based bound was found.

The comparison establishes the gain; the search supports, but cannot prove, priority. The field is small and the strongest baseline is a single v1 preprint, so concurrent or unreleased work could exist. The claimed contribution is a simple damped accelerated method with a log-free O(√T + α²T) guarantee for relative gradient error in the convex case.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
