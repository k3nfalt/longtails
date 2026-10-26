# RecursiveAnchorKmSmoothBanach: novelty assessment

[`result`](../../LongTails/Theorems/RecursiveAnchorKmSmoothBanach.lean) proves the following. Take a separable real Banach space that is 2-uniformly smooth in Xu's form, with constant K. Let T be nonexpansive on the whole space, with a fixed point x⋆ satisfying ‖x₀−x⋆‖ ≤ D. Assume the oracle is single-sample, IID, unbiased and has native-norm variance at most σ² ([setup](../../LongTails/Setups/StochasticFixedPointSmoothBanach.lean)). Under these assumptions, recursive anchoring with single-sample stochastic KM inner loops ([`tunedAnchorKm`](../../LongTails/Algorithms/RecursiveAnchorKm.lean)) returns its last stage iterate x̂ with E‖x̂−Tx̂‖ ≤ ε.

**Proved complexity.** Write ℓ = log₂(1+D/ε)+4. The budget is ⌈ℓ(16+20D/ε+2048Kσ²ℓ²/ε²)⌉, which gives

  **O( (1 + D/ε)·log(2+D/ε) + Kσ²·log³(2+D/ε)/ε² )** oracle calls, valid for all K ≥ 0, D > 0, σ ≥ 0 and ε > 0.

Here D is the initial distance to x⋆, σ the noise level, K the smoothness constant (K = 1 in Hilbert space, K = p−1 for ℓ_p and L_p with p ≥ 2) and ε the target expected residual.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Diakonikolas–Guzmán–Martínez-Rubio, [arXiv:2609.09524](https://arxiv.org/abs/2609.09524) v1 (8 Sep 2026), Thm 5 / Cor 6. Applies to weak type-2 norms, which include 2-smooth ones with type constant ≲ √K. | Õ(D/ε + KDσ²/ε³) with high probability, giving the same expected-residual order with δ = ε/(2D). Their polylogs were not extracted. → O((1+D/ε)log + Kσ²log³/ε²) | ε⁻³ → ε⁻² noise term, a gain of order D/ε up to logs. The gain survives when Kσ² ≫ ε²·polylog(D/ε) and D/ε ≫ log³(D/ε). | None. Their class (type-2 norms, constrained compact self-maps) is broader. | None. They give high probability; this result gives only expectation. | Needs 2-uniform smoothness, not type 2. Excludes ℓ∞-type norms. Requires T nonexpansive on all of E. Expectation only. |
| Lee, [arXiv:2610.26484](https://arxiv.org/abs/2610.26484) v1 (19 Oct 2026), Thm 3. Special case: finite-dimensional ℓ_p with 2 ≤ p < ∞. | O(D/ε + (p−1)Dσ²/ε³) → O((1+D/ε)log + (p−1)σ²log³/ε²) | Better when (p−1)σ² ≫ ε²log(D/ε) and D/ε ≫ log³(D/ε). Example: ℓ₄ with σ = D = 1 gives ε⁻³ → ε⁻²log³(1/ε). **Worse** by a factor log(D/ε) when (p−1)σ² ≲ ε². | ℓ_p^d → every 2-smooth space, including infinite-dimensional L_p and S_p. | None: both give the expected last iterate. | One extra log on the D/ε term. |
| Shehu, [arXiv:2610.00295](https://arxiv.org/abs/2610.00295) v1 (26 Sep 2026), Thm 4.3. Same class. | O(D/ε + KD²σ²/ε⁴) → O((1+D/ε)log + Kσ²log³/ε²) | Noise term improves by a factor (D/ε)²/log³(D/ε). | None | None | One extra log on the D/ε term. |
| Chen–Luo RAIN, [arXiv:2208.05925](https://arxiv.org/abs/2208.05925) (JMLR 2024), Thm 4.2, applied to F = I−T as in Shehu's Thm 4.8. **Hilbert special case (K = 1).** | O((D/ε)log log(D/ε) + σ²log³(D/ε)/ε²) → O((D/ε)log(D/ε) + σ²log³/ε²) | Hilbert: **worse** by a factor log/log log on the D/ε term. Same noise term. | Hilbert → 2-smooth Banach. Monotonicity of I−T is no longer available, and the proof uses only norms and Xu's inequality. | None | None beyond the log. |

**Related results not used as baselines.** VR-GHAL ([arXiv:2607.09097](https://arxiv.org/abs/2607.09097), Cor 3) already gets ε⁻² in quadratically smoothable spaces, but only under a stronger samplewise-nonexpansive oracle. Under bounded variance alone it gets ε⁻⁵. Its §1 says it is "unclear" whether the ε⁻² Euclidean rate transfers to other norms.

**Standard-reduction check.** The result is not a substitution into one known theorem. Plain Tikhonov anchoring plus stochastic approximation (SA) in a 2-smooth norm gives Shehu's ε⁻⁴. DGM's recursive anchoring uses median-of-means at every step and gives ε⁻³. The result composes two known pieces:

- the outer schedule of DGM/RAIN, itself following Allen-Zhu's recursive regularization;
- single-sample SA on the strongly contractive regularized maps T_u, using the mean-square inequality from 2-uniform smoothness, as in Juditsky–Nemirovski ([0809.0813](https://arxiv.org/abs/0809.0813)) and contractive-SA analyses such as [2002.00874](https://arxiv.org/abs/2002.00874).

What the composition adds is showing that each stage costs Kσ²/(η_uΛ_u)² = O(Kσ²S²/ε²), where η_u is the stage accuracy target, Λ_u the cumulative anchor weight and S the number of stages. It also replaces RAIN's monotone, inner-product argument with a norm-only anchoring recursion. This is a natural combination, but none of the checked papers states it.

**Search coverage.** On 2026-10-26 I searched arXiv and the web for stochastic KM and Halpern methods, anchoring, and accretive and contractive SA in smooth Banach spaces. I read the theorem statements of the five papers above in full text, and found no earlier ε⁻² bound for this oracle beyond Hilbert space. All Banach-space baselines are unrefereed preprints from 2026. Concurrent work cannot be excluded. The infinite-dimensional extension of DGM (their footnote 2) was not checked in detail. The companion note's citations and its rate table agree with these sources.

## Conclusion

**Yes: on 2-uniformly smooth spaces that are not Hilbert, the proved noise term drops from ε⁻³ to ε⁻², up to logarithms.**

The strongest previous bounds for this oracle (unbiased, bounded variance, no samplewise regularity) are Diakonikolas–Guzmán–Martínez-Rubio's recursive anchoring and Lee's dual Halpern method on ℓ_p:

  prior: Õ(D/ε + KDσ²/ε³)  →  this result: O((1+D/ε)log(D/ε) + Kσ²log³(D/ε)/ε²).

The gain is a factor of about D/ε whenever Kσ² ≫ ε²log(D/ε) and D/ε ≫ log³(D/ε). In the low-noise regime Kσ² ≲ ε², the result loses a log(D/ε) factor to Lee. In Hilbert space it adds nothing, because Chen–Luo's RAIN already gives the same noise term with a smaller deterministic log.

VR-GHAL's author called this transfer "unclear", while Shehu treated ε⁻³ as the best rate for weak type-2 norms. The improvement is meaningful for ℓ_p, L_p and Schatten-p spaces with p > 2. It shows the ε⁻³ lower bound comes from ℓ∞-type geometry rather than from non-Hilbert norms in general. The mechanism is a composition of known ingredients, and the guarantee holds only in expectation, whereas DGM's bound holds with high probability. Priority rests on a search of very recent preprints and could be affected by concurrent work.

What can be claimed: the first ε⁻²-type expected-residual complexity for nonexpansive maps with a bounded-variance oracle in general 2-uniformly smooth Banach spaces, matching the Hilbert rate up to K and logarithms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
