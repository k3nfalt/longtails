# Scion descent–ascent for generalized-smooth stochastic NC-SC minimax: novelty assessment

The [theorem](../../LongTails/Theorems/ScionGdaMinimax.lean) proves the following. Take the [setup](../../LongTails/Setups/MinimaxLmo.lean) and run [constant-schedule `lmoGda`](../../LongTails/Algorithms/MinimaxLmoGda.lean): a momentum-LMO (Scion) step on `x` in an arbitrary norm `N`, and a clipped single-sample stochastic gradient ascent step on unconstrained Euclidean `y`. The output is `x_J` with `J` uniform, and it satisfies `E‖∇Φ(x_J)‖_⋆ ≤ ε`. This holds for every `f` that is μ-strongly concave in `y` and locally `(L₀,L₁)`-smooth in the mixed distance `N(Δx)+‖Δy‖`, given unbiased, IID, bounded-variance oracles (`σx`, `σy` in ℓ₂), a warm start `‖y₁−y*(x₁)‖ ≤ W` with `32L₁W ≤ 1`, and `Φ(x₁)−inf Φ ≤ Δ`. No gradient bound along the iterates, a.s.-bounded noise or batching is assumed.

**Proved complexity** (one joint stochastic gradient per iteration). Write κ = L₀/μ and Ξ = 2+κ+L₀Δ/ε²+ζσx/ε+σy/ε+L₀W/ε+L₁ε/L₀. Then

  N = O( (1+κ) · [1 + L₁√((1+κ)(Δ/L₀+ε²/L₀²)) + (L₁ε/L₀) log Ξ]⁴ · [1 + L₀Δ/ε² + L₀W/ε + ζσx/ε + √((1+κ)(1+L₀Δ/ε²))] · [ζ²σx²/ε² + κ²(σy²/ε² + √((1+κ)(1+L₀Δ/ε²)) + log Ξ)] ).

Here ζ converts ℓ₂ to the dual norm (`‖u‖_⋆ ≤ ζ‖u‖₂`), and W is the warm-start radius. As ε→0 with σ > 0, the leading term is (1+κ)Λ⁴L₀Δ(ζ²σx²+κ²σy²)/ε⁴, with Λ = 1+L₁√((1+κ)Δ/L₀). Even with σx = σy = 0, the budget keeps a term κ^{7/2}Λ⁴(L₀Δ)^{3/2}/ε³. At L₁ = 0 the warm-start condition is vacuous.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gao–Liu, NSGDA-M, [arXiv:2603.04940v2](https://arxiv.org/html/2603.04940v2), Thm 3.6 (preprint, v2 2026-08-03, **prior**). Euclidean x, same local (L₀,L₁) type, Y = ℝᵐ or compact | Bound C δ^{-3/4}T^{-1/4} + G_Φδ. With δ = ε/(2G_Φ), this gives O(C⁴G_Φ³/ε⁷). I did not expand C. → O((1+κ)Λ⁴L₀Δ(ζ²σx²+κ²σy²)/ε⁴ + lower order) | ε⁻⁷ → ε⁻⁴ for fixed other parameters | They need ‖∇Φ(x_t)‖ ≤ G_Φ a.s. along the iterates (a condition on the algorithm). Here it is removed. | Same output criterion (expected primal-gradient norm at a random iterate). Their warm start √δ/(16L_{x,1}) → 1/(32L₁), which is weaker | Compact Y not covered here; this method clips the y-step and uses an LMO on x |
| Gao–Liu v2, Thm 3.5 (same paper). **Special case:** a.s.-bounded x-noise and sub-Gaussian y-noise | O(ε⁻⁴ log(1/(εδ))) with probability 1−δ (constants not expanded) → expectation ε⁻⁴ | Not comparable: different output criterion | Bounded/sub-Gaussian noise → bounded variance only | A high-probability bound does not yield an expectation bound without control on the bad event. Conversely, Markov's inequality on this result gives only a poly(1/δ) dependence | Theirs is high-probability with log(1/δ). This result is expectation only |
| Xian–Chen–Huang, generalized SGDA, [ICML 2024](https://proceedings.mlr.press/v235/xian24a.html), Thm 4.13 / Cor 4.14 | O(κ³ε⁻⁴) SFO with probability 1−δ, using batches b_x = O(ε⁻²) and b_y = O(κε⁻²). T = κ²/(δ²ε²), and the hidden constants ℓ(2G_x) grow with 1/δ → single-sample expectation ε⁻⁴ | Not comparable: different criterion. In ε both are ε⁻⁴ | Incomparable classes: theirs allows a general sub-quadratic ℓ(‖∇f‖). Here N is non-Euclidean on x | ε⁻²-size batches → one sample. poly(1/δ) probability → expectation | Both need a warm start. Λ⁴ here versus their ℓ(2G_x) factors |
| Wu et al., Localized-Prox, [arXiv:2610.00229v2](https://arxiv.org/html/2610.00229), Thm 3.4 (preprint, v1 2026-09-22, **prior**). **Special case L₁ = 0**, Euclidean, σ² = σx²+σy² | Õ(√κLΔ/ε² + κLΔσ²/ε⁴ + κ²σ²/ε² + √κ log₊(G/(ε√κ))) → O(κLΔ(σx²+κ²σy²)/ε⁴ + κ^{7/2}(LΔ)^{3/2}/ε³ + …) | Worse: by κ² in the σy term and by an ε⁻³ term versus ε⁻² in the deterministic part. Same order only when κσy ≤ σx | None. Their lower bound (same theorem) applies via Markov, so the σy term is κ² from optimal | Their criterion is probability 2/3, which this result also gives via Markov. Expectation is stronger, but no stronger complexity results | Theirs is multi-loop; this one is single-loop and allows an arbitrary norm on x |

**Reduction check and proof ancestry.** I found no reduction from the L₁ = 0 theory. Taking the effective smoothness L₀+L₁G requires an a priori bound G on ‖∇Φ‖ along stochastic iterates. Bounded variance does not give such a bound, which is exactly why Gao–Liu's Thm 3.6 assumes G_Φ. The new mechanism is the following. The clipped y-step bounds the tracking-error increments, so a Bernstein-type exit bound decays faster than the deterministic bad-event growth e^{O(L₁Δ/ε)}. That is what lets the expectation be closed without G_Φ. The x-side descent is ordinary LMO-momentum analysis (Pethick et al.'s uSCG/Scion; Cutkosky–Mehta normalized momentum), measured against ∇Φ via Danskin's formula.

**Search coverage** (2026-11-03 UTC). I searched arXiv, PMLR (ICML/AISTATS) and the web for generalized/relaxed-smooth minimax, NC-SC stochastic GDA, and LMO/Muon/non-Euclidean descent–ascent. I read the Gao–Liu v1/v2 abstracts and v2 theorems, Xian et al. §4.1.3, Yang et al. ([AISTATS 2022, arXiv:2112.05604](https://arxiv.org/abs/2112.05604)) Thm 3.1/Cor 4.1, and Wu et al. Thm 3.4. Gao–Liu v1 (2026-03-05) claimed O(ε⁻⁴) in expectation. In v2 that claim is replaced by the G_Φ-dependent T^{-1/7} rate. I saw no explicit retraction notice, so the companion note's word "retracted" is an inference. I did not check v1's proof. On the L₁ = 0 overlap, Yang et al.'s single-sample Stoc-AGDA (O(lκ²Δ/ε² + lκ⁴Δσ²/ε⁴), direct E‖∇Φ‖) is beaten by this result. Their Stoc-Smoothed-AGDA (κ², plus a κ^{5/2}σ²/ε² post-processing term) beats this result in the σy term. Wu et al. dominates both. The companion note's other citations match what I checked, but I did not verify SAPD+ or SPDE. I found no prior LMO/non-Euclidean minimax result. The result is uncommitted in the local tree, so it was introduced on or after 2026-11-03. I did not run a build.

**Conclusion**

**Yes, it covers new instances: it gives the first single-sample, bounded-variance ε⁻⁴ expectation guarantee I found for NC-SC minimax under (L₀,L₁)-smoothness with L₁ > 0.** The strongest baseline on that class is Gao–Liu's NSGDA-M expectation bound (Thm 3.6, v2):

| | calls for E‖∇Φ‖ ≤ ε | extra requirement |
|---|---|---|
| Gao–Liu v2, Thm 3.6 | O(C⁴G_Φ³ε⁻⁷) | ‖∇Φ(x_t)‖ ≤ G_Φ a.s. along the iterates |
| this result | O((1+κ)Λ⁴L₀Δ(ζ²σx²+κ²σy²)ε⁻⁴ + lower order) | warm start 32L₁W ≤ 1 |

Gao–Liu's ε⁻⁴ result (Thm 3.5) needs a.s.-bounded and sub-Gaussian noise and is high-probability. Xian et al. need ε⁻²-size batches and give poly(1/δ) probability bounds.

The tradeoffs are real. The L₁ cost Λ⁴ multiplies the leading term. The σy term carries κ³, and there is an ε⁻³ term even without noise. At L₁ = 0, Wu et al.'s method is better by κ² in the σy term. So nothing improves on Lipschitz-smooth problems, apart from allowing a non-Euclidean x-geometry.

The comparison proves that, for L₁ > 0, the assumption G_Φ is removed and the rate improves from ε⁻⁷ to ε⁻⁴. Priority is supported only by my search, and the main competitors are themselves recent preprints. The claimable contribution is an ε⁻⁴ expected-stationarity guarantee for single-sample LMO descent–ascent under generalized smoothness with only bounded variance, obtained with a clipping-plus-exit-probability argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
