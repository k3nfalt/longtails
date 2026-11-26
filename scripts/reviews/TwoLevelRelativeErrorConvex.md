# Two-level acceleration under relative gradient error: novelty assessment

[`TwoLevelRelativeErrorConvex.result`](../../LongTails/Theorems/TwoLevelRelativeErrorConvex.lean) proves a deterministic guarantee: for convex L-smooth f on a real Hilbert space, a minimizer within distance R of x₀, and an adaptive oracle whose every reply satisfies ‖g − ∇f(x)‖ ≤ α‖∇f(x)‖, the returned point satisfies f(x_out) − f(x⋆) ≤ ε on every seed ([setup](../../LongTails/Setups/RelativeErrorSmoothConvex.lean), [algorithm](../../LongTails/Algorithms/TwoLevelRelativeErrorConvex.lean)). The algorithm compares two budgets before its first query: the existing damped single loop, or a two-level scheme. The two-level scheme runs an outer damped accelerated proximal loop with μ = α⁴L and solves each inner problem with the mixed-error strongly convex method.

**Complexity.** Here T = LR²/ε, α is the relative error, and the algorithm knows L, α, R and ε. For 0 < α ≤ 1/32 and T ≥ 1, the budget is
  N = O( min{ √T + α²T, (α⁻² + √T + α⁴T)·log(1/α) } ).
Otherwise (any α < 1) it is O(√(T/(1−α)) + α²T/(1−α)), and N = 0 when R = 0. This bound comes from the exact `min N₀ (K·m)` in the budget. The note's estimate K·m ≤ 1711(α⁻² + √(12e)·√T + 1536e·α⁴T)·log(1/α) is consistent with the definitions.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository single loop, [AcceleratedRelativeErrorConvex](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean) (prior: initial commit, 2026-10-14; same setup) | ⌈7√(T/(1−α)) + 11α²T/(1−α)⌉ → min of that and (α⁻² + √T + α⁴T)·log(1/α) | Never worse. Asymptotically better when T^{-1/4}√log(1/α) ≪ α ≪ 1. At α = T^{-1/8}: T^{3/4} → √T·log T. With the actual constants, a gain needs α ≲ 7·10⁻⁴ and T ≳ 2·10²¹ (I recomputed this at α = 3·10⁻⁴). | None | None: both are deterministic last-iterate methods using L, α, R and ε | The branch needs α ≤ 1/32 and T ≥ 1. The constants are huge. |
| Vasin–Tyurin–Gasnikov, [arXiv:2610.24863](https://arxiv.org/abs/2610.24863) v1 (2026-10-17, preprint), Thm 3.3 with δ = 0 | O((√T + α²T)·log T) for α ≤ 1/3 → as above | Removes the log T factor and improves α²T to α⁴T·log(1/α) in the regime above. | None (their composite-error model is broader. Only its δ = 0 slice is compared.) | Their method is adaptive in L (line search). The selected method needs L. | Their adaptivity in L is lost. |
| Vasin–Gasnikov, [arXiv:2603.12376](https://arxiv.org/abs/2603.12376) v1 (2026-03-12, preprint), Thms 7.2 and 9.3 | O(max{√T, αT}·log T) for α ≤ 1/3 (tuning β to α) → as above | Polynomial gain for T^{-1/2} ≪ α ≪ 1, e.g. α = T^{-1/4}: T^{3/4}·log T → √T·log T. | None | None | None beyond α ≤ 1/32 for the new branch |
| Repository hand-proved "two-level" proposition, [AcceleratedRelativeErrorConvex.md, Tightness](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.md) (prior, 2026-10-14; not formalized) | O((α⁻² + √T + α⁴T)·log(2 + T/α²)) for α ≤ 1/27 → O((α⁻² + √T + α⁴T)·log(1/α)) for α ≤ 1/32 | The logarithm improves from log(T/α²) to log(1/α). | None | None | The α range shrinks slightly (1/27 → 1/32). |

**Reduction and mechanism.** The result is essentially a composition of existing pieces. The outer loop applies the repository's damped single-loop method to the Moreau envelope M_μ. There ∇M_μ(y) = μ(y − p), and μ(y − u) is a relative-σ estimate of it with σ = 16α. That outer loop yields K ≍ √(α⁴T) + α⁶T. The inner method is the repository's mixed-error strongly convex solver at condition number α⁻⁴, costing m ≍ α⁻²·log(1/α) per step. The only adaptation is converting the inner function-value accuracy into the relative proximal error and the f(u) gap. Proof ancestry: inexact accelerated proximal point (Güler 1992; Catalyst, Lin–Mairal–Harchaoui, [arXiv:1712.05654](https://arxiv.org/abs/1712.05654)). These supply the outer template but not the damped handling of a non-vanishing relative proximal error.

**Lower-bound status.** The result (like the earlier sketch) gives Õ(√T) for T^{-1/4} ≪ α ≪ T^{-1/8}. This contradicts a reading of [arXiv:2603.12376](https://arxiv.org/abs/2603.12376), Thm 10.2(1), as an Ω(α²T) lower bound for this oracle class. The stated exponent uses log_{LR²/ε}(α) and is likely mistyped. Per the paper, its proof transfers absolute-noise hard instances. I could not read Appendix G, so this conflict is noted, not adjudicated.

**Search coverage (2026-11-26).** I searched arXiv and the web for relative-error and inexact-gradient acceleration, Catalyst/proximal-point methods, and the papers cited in the note. I read the HTML theorem statements of 2603.12376 and 2610.24863 (Appendix G of 2603.12376 was not accessible). Kornilov et al. ([2310.00506](https://arxiv.org/abs/2310.00506), α²LR² floor) and the strongly convex works ([2102.02921](https://arxiv.org/abs/2102.02921), [2503.06628](https://arxiv.org/abs/2503.06628)) do not give a better convex bound. I found no published α⁴T bound. The companion note's descriptions of the checked theorems agree with what I read. The note correctly credits the earlier repository sketch.

## Conclusion

**Yes, there is an asymptotic gain over all published bounds, but it repeats a two-level bound the repository had already stated, now with a smaller logarithm and a formal proof.** The strongest baseline is the repository's own single-loop theorem; the best published one is Vasin–Tyurin–Gasnikov Thm 3.3, which adds a log T factor.

| | calls (T = LR²/ε) |
|---|---|
| single loop | √T + α²T |
| this result | min{√T + α²T, (α⁻² + √T + α⁴T)·log(1/α)} |

The gain is polynomial when T^{-1/4}√log(1/α) ≪ α ≪ 1, reaching about T^{1/4}/log T at α = T^{-1/8}. With the proved constants, though, it appears only for α ≲ 7·10⁻⁴ and T ≳ 10²¹. It is never worse, because the budget takes the minimum.

My literature search found no prior α⁴T bound, but the argument is close to a routine composition. It is a Catalyst-style outer loop running the existing damped method on the Moreau envelope with relative error 16α, plus the existing strongly convex solver. The same scheme and bound, with log(2 + T/α²), were hand-proved in the repository's note from its first commit. What can be claimed is a machine-checked two-level bound that removes T from the logarithm and beats published α²T rates in a regime that is asymptotic only.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
