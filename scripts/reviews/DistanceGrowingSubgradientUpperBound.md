# Novelty assessment: DistanceGrowingSubgradientUpperBound

[Theorem](../../LongTails/Theorems/DistanceGrowingSubgradientUpperBound.lean) · [Setup](../../LongTails/Setups/DistanceGrowingSubgradient.lean) (reuses [TerminalClippingConvex](../../LongTails/Setups/TerminalClippingConvex.lean) without its algorithm restriction) · [Algorithm](../../LongTails/Algorithms/LocalizedClippedSubgradient.lean)

**Guarantee.** Consider a convex `f` on a closed convex set `X`, given IID stochastic relative subgradients with `E‖g(x)‖² ≤ G² + B²‖x−x₀‖²` on `X`, exact projections onto `X`, and known `x₀, R, B, G, ε, δ`. The method is clipped stochastic subgradient descent. Each step is projected onto the ball `B(x₀,R)` and then onto `X`, and the output is the uniform average. It returns a feasible point with `P(f(x̄) − min_X f > ε) ≤ δ`. This holds for all `B, G ≥ 0`, `R, ε > 0`, `0 < δ < 1`, and every dimension `d`.

**Complexity** (one unit per sampled subgradient or projection; `R` bounds `‖x₀ − x*‖`):

  N = 0 if GR ≤ ε, and otherwise N = 2⌈1024 R²(G² + B²R²) log(8/δ)/ε²⌉ = O(R²(G² + B²R²) log(8/δ)/ε²).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Parletta–Paudice–Pontil–Salzo, [arXiv 2208.08567v2](https://arxiv.org/abs/2208.08567) (SIAM J. Math. Data Sci. 6(4), 2024), Thm 2(iii) + Cor. 1 (finite horizon, uniform weights). Applied through the localization reduction below; prior | O(R²(G²+B²R²) log(1/δ)/ε²) → O(R²(G²+B²R²) log(8/δ)/ε²) | None: same order | None. Their bounded-domain/Lipschitz/variance class covers the localized problem | None. Both give a high-probability bound for the averaged iterate with known parameters | Theirs states `δ ≤ 2/e`. Use `δ' = min(δ, 2/e)`, which costs only a constant |
| Liu–Zhou, [arXiv 2303.12277v3](https://arxiv.org/abs/2303.12277), Thm 3 (clipped projected SGD, known `T`, `σ`), applied to the localized problem; prior | O(R²(G²+B²R²) log²(1/δ)/ε²) → O(R²(G²+B²R²) log(8/δ)/ε²) | log(1/δ) factor (dominated by Parletta et al.) | None (theirs covers unbounded `X` when subgradients are uniformly bounded) | None | None |
| Alacaoglu–Malitsky–Wright, [arXiv 2504.09951v3](https://arxiv.org/abs/2504.09951), Assumption 3.1 and Cor. 3.4 (expected gap of a weighted Halpern average), with `B' = max(B, G/R)` and Markov's inequality; prior | O(R²(G²+B²R²)/(ε²δ²)) → O(R²(G²+B²R²) log(8/δ)/ε²) | δ⁻² → log(8/δ), for every δ < 1 | None. Same initial-point B–G class | Expected gap → high-probability gap. Their updates do not use the ball projection | Theirs needs only `B`, not `R`, in the updates |
| Repository [ClippedBgLastIterate](../../LongTails/Theorems/ClippedBgLastIterate.lean) (fixed-method setup); prior in repository | O((BR²+G²/B)² log²(8/δ)/ε²) → O(R²(G²+B²R²) log(8/δ)/ε²) | Removes the `G⁴/B²` term (a factor ≈ G²/(B²R²) when `BR ≪ G`) and one log | `B, G > 0` → `B, G ≥ 0` | None. The output is weaker: last iterate → average | Loses the last-iterate guarantee |

**Reduction check.** On `K = X ∩ B(x₀,R)`, three facts give a bounded-domain problem:
- `E‖g‖² ≤ v := G² + B²R²`.
- The mean subgradient has norm `L ≤ √v`.
- The variance is `σ² ≤ v`, and the diameter is `D ≤ 2R`.

The map `P_X∘P_ball` sends points into `K` and satisfies `‖P(y) − u‖ ≤ ‖y − u‖` for `u ∈ K`. Parletta et al.'s error decomposition (Lemma 2, eq. A.2) uses only this inequality and the diameter.

Set `β̄ = √v` and `γ ≍ R/√v` in their Cor. 1. This gives gap `O(R√v·√(log(2/δ)/k))` for `k ≳ log(2/δ)`. That condition holds automatically because `R²v ≥ G²R² > ε²`.

No new mechanism is required. Proof ancestry: Freedman-type martingale concentration for clipped SGD supplies the single `log(1/δ)`. The local ingredients are the localization and the zero-call `GR ≤ ε` branch.

**Search coverage.** On 2026-11-18 (UTC) I read the theorem statements and relevant proof steps of the four sources above. I also checked Nazin–Nemirovsky–Tsybakov–Juditsky ([arXiv 1907.02707](https://arxiv.org/abs/1907.02707), Thm 1). It gives the same sub-Gaussian rate but assumes a smooth stochastic part, so I did not use it as a baseline. I did not verify the companion note's arXiv 2610.00260 and 2611.07334 citations.

The theorem was introduced in commit `6442d923` (2026-11-18 21:03 UTC), so all baselines predate it. The companion note itself concedes that "known clipped methods for a uniform second moment already explain the upper rate after localization". It places the contribution in the separate lower bound, which is not assessed here.

## Conclusion

**No: this upper bound is a standard corollary of known clipped-subgradient theory.** If you project onto the known ball `B(x₀,R)`, the distance-growing moment condition becomes a uniform bound `v = G² + B²R²`. Parletta et al.'s (2022/2024) high-probability theorem for clipped projected subgradients then applies directly:

| | Calls for `P(gap > ε) ≤ δ` |
|---|---|
| Parletta et al. Cor. 1 after localization | O(R²(G²+B²R²) log(1/δ)/ε²) |
| This theorem | O(R²(G²+B²R²) log(8/δ)/ε²) |

The two bounds have the same order in every parameter regime. Both need the same known parameters and both output an average. Neither retains an advantage over the other in any regime.

The gains this theorem does prove are only over weaker baselines. Against Markov applied to Alacaoglu–Malitsky–Wright's expected bound, the confidence factor drops from `δ⁻²` to `log(1/δ)`. Against the repository's last-iterate theorem, it removes a `G⁴/B²` term and one logarithm and allows `B = 0` or `G = 0`, but gives up the last-iterate output. Both gains are matched by the reduction above.

What can be claimed is a clean, formally verified implementation of known rates. Its one minor practical detail is that projecting onto the ball and then onto `X` avoids projecting onto their intersection. Any significance of this research question lies in the companion lower bound, not in this upper bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
