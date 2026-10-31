# Novelty assessment: LocalFiniteSumAcceleration

The [theorem](../../LongTails/Theorems/LocalFiniteSumAcceleration.lean) ([setup](../../LongTails/Setups/GeneralizedSmoothFiniteSum.lean), [algorithm](../../LongTails/Algorithms/LocalFiniteSumAcceleration.lean)) covers `F = n⁻¹Σᵢfᵢ` on a real Hilbert space, where each `fᵢ` is convex with a continuous gradient and is symmetrically `(L₀,L₁)`-smooth. The minimizer `x*` need not be shared: it is only required that `n⁻¹Σ‖∇fᵢ(x*)‖ ≤ G`. Using exact component value-and-gradient calls, and knowing `L₀,L₁,G,R,Δ`, a restarted, amplified, importance-sampled accelerated variance-reduction method returns a point whose expected gap satisfies `∫(F(out) − F*) dP ≤ ε`. The output is either `x₀` or the best final snapshot over independent trials.

**Proved complexity.** Here `L₀ > 0` and `L₁ ≥ 0` are the smoothness constants, `G ≥ 0` is the mean optimum component-gradient norm, `R ≥ ‖x₀−x*‖`, `Δ ≥ F(x₀)−F*`, and `n` is the number of components. The public budget `⌈2²⁴[n(1+L₁R)log²(2+Δ/ε) + √(n(L₀+L₁G)R²/ε)·log(2+Δ/ε)]⌉` gives

  `O( n(1+L₁R)·log²(2+Δ/ε) + √(n(L₀+L₁G)R²/ε)·log(2+Δ/ε) )` component calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Varag (Lan–Li–Zhou, [NeurIPS 2019](https://proceedings.neurips.cc/paper_files/paper/2019/file/add5aebfcb33a2206b6497d53bc4f309-Paper.pdf), Thm 1) run on `X = B(x₀,R)` with `qᵢ ∝ Lᵢ`. **Prior, verified reduction; finite-dimensional overlap** | `n·log(2+n) + e^{L₁R}·√(n(L₀+L₁G)R²/ε)` → `n(1+L₁R)log²(2+Δ/ε) + √(n(L₀+L₁G)R²/ε)·log(2+Δ/ε)` | The leading factor improves from `e^{L₁R}` to `log(2+Δ/ε)`, a gain that is exponential in `L₁R`. It holds when `e^{L₁R} ≫ log(2+Δ/ε)` and `e^{L₁R}√((L₀+L₁G)R²/(nε)) ≫ (1+L₁R)log²(2+Δ/ε)`. Example: `(L₀+L₁G)R²/ε = n(L₁R)²` gives `n·L₁R·e^{L₁R} → n·L₁R·log²` | None: the classes are the same on ℝᵈ | None: both give an expected objective gap at a returned point | **Worse when `L₁R = O(1)`**, by up to a `log(2+Δ/ε)` factor on the `√n` term and `log²(Δ/ε)` versus `log n` on the `n` term. Varag needs only gradients and `L₀,L₁,R`. This method also needs function values, `G` and `Δ` |
| Gorbunov et al., (L₀,L₁)-SGD ([arXiv:2409.14989v2](https://arxiv.org/abs/2409.14989), ICLR 2025), Thm 7.2 under Assumption 7.1. **Prior; special case of a shared minimizer, i.e. G = 0** | `O(L₀R²/ε)` single-component gradients. This bounds `min_k E[min{νL₀/(4nL₁²), F(x_k)−F*}]`, so it is meaningful only if `ε < νL₀/(4nL₁²)` → with `G=0`: `n(1+L₁R)log²(2+Δ/ε) + √(nL₀R²/ε)·log(2+Δ/ε)` | Accelerated rate. Gain factor about `√(L₀R²/(nε))/log²(2+Δ/ε)` whenever `L₀R²/ε ≫ n(1+L₁R)²log⁴(2+Δ/ε)` | Shared minimizer (`∇fᵢ(x*) = 0` for all `i`) → no interpolation required (`G > 0` allowed) | Truncated min-over-iterates expectation (no computable output) → expected untruncated gap of the returned point | Gorbunov's method uses gradients only and does not need `Δ` or restarts. This method needs values, `Δ` and `G` |

To check the Varag row, note that on `B(x₀,R)` Grönwall's inequality for the symmetric condition gives `‖∇fᵢ‖ ≤ (‖∇fᵢ(x₀)‖+L₀/L₁)e^{L₁R} − L₀/L₁`. Applying the same bound once more from `x*` gives `n⁻¹ΣLᵢ ≤ e^{2L₁R}(L₀+L₁G)`. The constants `Lᵢ` can be computed from `n` calls at `x₀`. Projection onto the ball is closed-form, and `D₀ = 2Δ + 1.5·n⁻¹ΣLᵢ·R² ≤ 2.5·n⁻¹ΣLᵢ·R²`, because `F` is smooth on the ball and `∇F(x*) = 0`.

Full-gradient generalized-smooth accelerated theorems do not transfer to `F`. Because component gradients can cancel, `‖∇²F‖` is controlled by the gap, not by `‖∇F‖`. Lobanov's gap-dependent `(H₀,H₁)` method ([arXiv:2608.04884v1](https://arxiv.org/abs/2608.04884), Thm 5; prior, Aug 2026) would be the natural route. However, it needs `f*`, an exact segment search and the level-set radius `R̃ ≥ R`, and it pays `n` calls per gradient. So it does not give a bound comparable with this oracle.

The companion note mentions polynomial-in-`L₁R` reductions, namely full-gradient similar-triangles and componentwise extension followed by variance reduction. These are its own reconstructions. They are neither published theorems nor checked here, so they are not table rows.

**Reduction check and ancestry.** The plain reductions I checked lose `e^{Θ(L₁R)}`: a ball constraint, or a single global curvature bound, followed by Varag, VRADA or Katyusha. Snapshot-measured importance weights combined with a stopped accelerated energy, which keeps queries in moving local balls, is what removes that factor. The ingredients are standard: similar-triangles variance reduction (Varag/VRADA), local `(L₀,L₁)` estimates (Gorbunov et al.), and independent amplification. I did not verify the Lean proof beyond reading the statement and the budget.

**Search coverage (2026-10-26 UTC).** I searched arXiv and the web for variance reduction, finite sums and acceleration under `(L₀,L₁)`, ℓ-smoothness and local smoothness, and read Varag Thm 1, Gorbunov §7–8 and Lobanov Thm 5. ARC-SG ([2609.06555](https://arxiv.org/abs/2609.06555)) is single-stochastic-oracle and not finite-sum. Tovmasyan et al. ([2502.03401v2](https://arxiv.org/abs/2502.03401)) need interpolation and proximal oracles. Variance-reduced clipping ([2303.00883](https://arxiv.org/abs/2303.00883)) is nonconvex. I did not check ARC-SG's Appendix F or Vainsencher et al. (2015) myself. Git dates the theorem to `ae23fe4` (2026-10-26), after all cited work. The note's claimed `n^{1/4}` gain is relative to its own unverified reconstructions, not to a published baseline.

## Conclusion

**Yes. Without a shared minimizer, it is the first checked accelerated finite-sum bound for componentwise (L₀,L₁)-smooth convex sums that is polynomial in L₁R.**

The strongest bound I could derive from a published theorem runs Varag inside the ball `B(x₀,R)`. Its local smoothness constants carry a factor `e^{L₁R}`, with `T̄ = (L₀+L₁G)R²/ε` and `ℓ = log(2+Δ/ε)`:

| | component calls |
|---|---|
| Varag on a ball | `n log n + e^{L₁R}·√(nT̄)` |
| this result | `n(1+L₁R)ℓ² + √(nT̄)·ℓ` |

The gain is exponential in `L₁R` once `e^{L₁R}` exceeds the logarithms. For example, if `T̄ = n(L₁R)²`, the bound drops from about `n·L₁R·e^{L₁R}` to `n·L₁R·ℓ²`. When `L₁R = O(1)`, Varag is better by logarithmic factors and needs neither function values nor `G` or `Δ`. With a shared minimizer, the result also accelerates Gorbunov et al.'s `O(L₀R²/ε)` SGD bound.

What is uncertain is whether a simpler polynomial-in-`L₁R` reduction exists, such as restarting on sublevel sets or locally extending the components. The companion note sketches such reductions but they were not checked; if one held, the gain would shrink to roughly `√n/log` on the accuracy term. The search found no prior result of this kind, but that does not prove priority.

The contribution that can be claimed is accelerated variance reduction for noninterpolating generalized-smooth finite sums, without the exponential `L₁R` cost of the standard ball-localized reduction.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
