# Novelty assessment: DistanceGrowingSubgradientLowerBound

The [theorem](../../LongTails/Theorems/DistanceGrowingSubgradientLowerBound.lean) proves a lower bound. In the [setup](../../LongTails/Setups/InterpolatedDistanceGrowingSubgradient.lean), the domain is unconstrained and every sample loss is convex and C^∞. All sample losses share one minimizer within distance R of x₀ and have the same gradient at x₀. The full second moment satisfies E‖g(x)‖² ≤ G² + B²‖x−x₀‖². Under these conditions, every randomized adaptive algorithm with any budget b ≤ ⌊R²(G²+B²R²)log(1/δ)/(2²⁸ε²)⌋ fails on some instance, meaning P(f(x̂)−f* > ε) > δ there. The algorithm class is unrestricted (`allowedAlgorithm` keeps its default value `True`), and the hard instance depends on the algorithm but not on its seed. The matching [upper algorithm](../../LongTails/Algorithms/LocalizedClippedSubgradient.lean) is the repository's companion result.

**Proved bound.** With d ≥ 2, B ≥ 0, G, R > 0, 0 < ε ≤ GR/65536 and 0 < δ ≤ 1/8, the necessary number of calls is

  N ≥ Ω( R²(G² + B²R²) · log(1/δ) / ε² ).

Here R bounds the initial distance, G² bounds the second moment at x₀, B is the distance-growth coefficient, ε is the objective accuracy and δ the failure probability. At these parameters the budget is at least 33. Projection queries count as calls; in the hard instance the projection is the identity.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon–Hinder, COLT 2024, [arXiv 2402.10898](https://arxiv.org/abs/2402.10898) Prop. 1b (§3.3). Lower bound for known-parameter high-probability SCO with ‖g‖ ≤ L a.s. Applies only at B = 0, with L = G. | Ω(G²R²log(1/δ)/ε²) → Ω(R²(G²+B²R²)log(1/δ)/ε²) | Stronger by a factor 1 + B²R²/G², which is unbounded when BR ≫ G. At B ≲ G/R the two bounds have the same order. | The hard class becomes a BG-0 growth class with a small moment at the anchor, and also satisfies interpolation, smooth convex samples and a deterministic anchor gradient. Because the hard class is smaller, the lower bound is stronger. | None. Both bounds concern the same high-probability objective gap. | Requires d ≥ 2, ε ≤ GR/65536 and δ ≤ 1/8. The range GR/65536 < ε < GR is left open. Sample smoothness is of order (G²+B²R²)/ε, so the bound does not apply to classes with a fixed sample-smoothness bound L_s. |
| Alacaoglu–Malitsky–Wright, [arXiv 2504.09951v3](https://arxiv.org/html/2504.09951v3#S3), Assumption 3.1 and Cor. 3.4. Upper bound on expected gap of order (3BR²+2G²/(3B))/√k. | Upper bound O(R²(G+BR)²/ε²) after replacing B by max(B, G/R) at constant δ; adding Markov's inequality costs δ⁻². This result adds a lower bound of the same order. | Not a speed-up. It shows that the B²R⁴/ε² dependence of the AMW rate is necessary up to constants. The paper states no convex lower bound under BG-0. | None. Since the lower class is nested in the AMW class, the bound also applies there. | None | Expectation upper bound compared with a high-probability lower bound. Failure with probability greater than δ = 1/8 already forces E gap > ε/8. |
| Repository upper bound [DistanceGrowingSubgradientUpperBound](../../LongTails/Theorems/DistanceGrowingSubgradientUpperBound.lean), same commit. Its class is broader and contains this one. | Upper 2⌈1024R²(G²+B²R²)log(8/δ)/ε²⌉ vs. lower ⌊R²(G²+B²R²)log(1/δ)/(2²⁸ε²)⌋ | Tight up to universal constants for δ ≤ 1/8 and ε ≤ GR/65536, since log(8/δ) ≤ 2log(1/δ). | — | — | Constant gap of about 2³⁸. |

**Reduction check.** No black-box rescaling of a uniform-moment hard instance works. A Carmon–Hinder instance with L ≈ BR would violate the moment bound G² at x₀, and the algorithm could query near x₀ where the noise is small. The construction therefore needs a tilt whose gradient vanishes at x₀, so that both instances give the same answer there, and a rare Bernoulli mask that keeps the samples convex and interpolating. With these, a two-point Le Cam argument gives the (1−q)^{n+1} > 2δ prefix bound. Each ingredient is familiar: two-point testing, rare masking, and distance-dependent hiding as in [Fazl et al., arXiv 2604.16620v1](https://arxiv.org/html/2604.16620v1) Thms 1–2. Those theorems are nonconvex, gradient-norm and in-expectation results, so they do not imply this one. Combining the ingredients in a convex setting with the moment bound holding at every point is the actual technical step, and it is short.

**Search coverage.** I searched on 2026-11-18 (UTC), covering arXiv and COLT/ICML/NeurIPS work on BG-0 or growing-variance noise, high-probability convex lower bounds, and interpolation lower bounds. Carmon–Hinder and AMW were read through partial HTML extraction, so Prop. 1b's exact wording is not quoted verbatim. I could not locate the companion note's Novoselov et al. citation (arXiv 2610.38354), and the Attia et al. citation was not checked. The result entered the repository in commit 6442d923 (2026-11-18 21:03 UTC), after all the cited prior work. The companion note's claims agree with the Lean statement.

## Conclusion

**Yes. In the regime BR ≫ G it proves a strictly larger necessary budget than any convex lower bound I found.** The strongest prior baseline is Carmon–Hinder's high-confidence bound for bounded stochastic gradients:

| | Necessary calls |
|---|---|
| Carmon–Hinder (B = 0) | Ω(G²R²log(1/δ)/ε²) |
| This result | Ω(R²(G²+B²R²)log(1/δ)/ε²) |

The bound holds for d ≥ 2, ε ≤ GR/65536 and δ ≤ 1/8. The gain is the factor 1 + B²R²/G²; at B ≲ G/R the two bounds coincide. It matches the companion upper bound and the AMW expected rate up to constants, so the R⁴B² cost of distance-growing moments is shown to be unavoidable. The hard class is also interpolating with a deterministic anchor gradient, so a small initial moment does not help.

What remains uncertain is priority, not the comparison. The proof uses standard testing tools, and a folklore version cannot be excluded; two 2026 citations in the companion note were not verified. The range GR/65536 < ε < GR is not covered, and nor are classes with bounded sample smoothness.

The claimable contribution is the first verified tight high-confidence lower bound for convex optimization under initial-point Blum–Gladyshev growth, which also holds under interpolation.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
