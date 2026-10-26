# Novelty assessment: accelerated composite optimization under total-gap curvature

[`CompositeGapAccelerated.result`](../../LongTails/Theorems/CompositeGapAccelerated.lean) ([setup](../../LongTails/Setups/CompositeGapSmooth.lean), [algorithm](../../LongTails/Algorithms/CompositeGapAccelerated.lean)) proves the following. Minimize F = f + ψ over a convex set Q in a Hilbert space. Here f is globally convex and differentiable, ψ is convex on Q, and exact Q-constrained prox minimizers exist. Assume f(y) ≤ f(x) + ⟨∇f(x), y−x⟩ + (H₀ + H₁(F(x)−F⋆))‖y−x‖² for every x ∈ Q and every ambient y with √H₁‖y−x‖ ≤ 1. Then restarted accelerated dual averaging, using exact gradient and prox calls, deterministically returns a final point x̂ ∈ Q with F(x̂) − F⋆ ≤ ε.

**Proved budget.** R ≥ ‖x₀−x⋆‖, Δ ≥ F(x₀)−F⋆, H₀, H₁ ≥ 0, ε > 0, and the method knows (H₀, H₁, R, Δ, ε). The total number of gradient plus prox calls is

  O( (1 + R√(H₀/ε + H₁)) · log(4 + R²(H₀/ε + H₁)) · log(2 + Δ/ε) ).

This is the Lean budget with the constant 8192 suppressed. There is no dimension factor.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/abs/2609.33415) (27 Sep 2026, preprint, prior), Thm 9 specialized to zero noise. **Only covers ψ ≡ 0, Q = E**; also [Lobanov arXiv:2608.04884v1](https://arxiv.org/abs/2608.04884) Thm 5 (needs exact line search, function values, and sublevel radius R̃) | Õ(log(Δ/ε) + R√(H₀/ε) + R√H₁·log(Δ/ε)) → the bound above | Worse on the overlap: an extra log(4+R²(H₀/ε+H₁)) factor on both terms, and log(Δ/ε) on the H₀ term | Unconstrained smooth f → composite f+ψ over convex Q with ∇f(x⋆) ≠ 0 (for example, exponential loss + ℓ₁ penalty or constraints) | None | Exact oracles only; deterministic results only. Thm 9 also covers stochastic and heavy-tailed noise |
| Repository [CompositeGeneralizedAccelerated](../../LongTails/Theorems/CompositeGeneralizedAccelerated.lean) (2026-10-14; not literature). Composite (L₀,L₁)-smoothness with ‖∇f(x⋆)‖ ≤ G | O(R√((L₀+L₁G)/ε) + (1+L₁R)·log(2+L₁R√(Δ/(L₀R²)))) → by my embedding sketch (H₀ ≍ L₀+L₁G, H₁ ≍ L₁², constants unverified), O((1 + R√((L₀+L₁G)/ε) + L₁R)·log(·)·log(2+Δ/ε)) | On the (L₀,L₁) overlap: None (worse by logs). On the δ-family below: δ⁻² → O(δ⁻¹ε⁻¹ᐟ²log²(1/(δε))), a gain when ε ≫ δ²·polylog(1/δ), e.g. δ⁻² → δ⁻³ᐟ²log² at ε = δ | Gradient-norm curvature → total-gap curvature. On the family, the (L₀,L₁) constant L₁ ≥ 1/δ, while the gap constants are H₀ = 2e, H₁ = e uniformly | No G needed to stop | Needs Δ. Ambient (not feasible-only) local model |
| Moreau smoothing of ψ, then Thm 9 of 2609.33415 (reduction derived in the note and checked in outline). **Only unconstrained, globally G_ψ-Lipschitz ψ** | Õ(R′√(H₀/ε) + R′G_ψ/ε + R′√H₁·log(Δ/ε)), where R′ is the distance to the smoothed minimizer (not bounded by R in general) → the bound above | Removes the R G_ψ/ε term: polynomial gain whenever G_ψ ≫ √(H₀ε) | Lipschitz ψ, Q = E → arbitrary convex ψ (constraints, non-Lipschitz regularizers) | None | Logarithmic factors. The reduction's R′ obstacle is unresolved in general |

**Reductions and mechanism.** Direct substitution fails. Applying the smooth-only theorems to F needs smooth ψ. Ball-smoothness constants can be exponentially large (e^{αR}) for exponential losses. AC-FGM ([Li–Lan, arXiv:2310.10082v3](https://arxiv.org/abs/2310.10082), Cor. 1) bounds complexity by the largest curvature encountered, which has no a-priori bound here. [Yang–Xian (JAMP 2026)](https://www.scirp.org/journal/paperinformation?paperid=150902), Thm 8, is unaccelerated and requires globally Lipschitz f. The new step is controlling the composite gap at extrapolation points from the cumulative prox objective, giving j(z) ≤ d + 2RG with no 1/A term and F(y)−F⋆ ≤ 2d, without a ball-intersection prox. I did not audit these Lean proofs. Proof ancestry: Xiao's accelerated regularized dual averaging ([JMLR 2010](https://jmlr.org/papers/v11/xiao10a.html), §7.1) supplies the energy algebra under global smoothness, and geometric restarts follow Lobanov et al. The localization argument is the additional work.

I checked the δ-family f = 2e^{δy}cosh x, ψ = |x| + 2δ|y|, x₀ = (0, 1/δ). The minimizer (0,0) is optimal by subgradients, and F⋆ = 2. ‖∇²f‖ ≤ 2f, f grows by at most a factor e within radius e^{−1/2}, and f ≤ F − F⋆ + 2, so H₀ = 2e and H₁ = e hold. Along (0, y), ∂ₓₓf = 2e^{δy} = ‖∇f‖/δ forces L₁ ≥ 1/δ.

**Search coverage.** On 2026-10-26 UTC I read theorem statements and setting sections of 2609.33415 and 2608.04884; both are unconstrained. I read the abstracts of 2609.06555 (unconstrained (L₀,L₁)) and the Yang–Xian composite PGD paper, and searched arXiv and the web for composite or proximal generalized-smooth acceleration. I did not read ICML, ICLR, or NeurIPS 2026 proceedings in full and did not re-derive 2609.33415's hidden logarithms. The result was introduced in commit 0dc2692 (2026-10-26), after all cited preprints. The companion note's characterization of these sources matches what I read.

## Conclusion

**Yes, in scope: this extends gap-curvature acceleration from unconstrained smooth problems to composite and constrained ones; it is not faster on the old classes.**

The strongest prior guarantee, Theorem 9 of Lobanov–Dvinskikh–Gasnikov (Sep 2026), applies only to unconstrained smooth f. On that overlap, the new bound matches it up to an extra log(R²(H₀/ε+H₁))·log(Δ/ε) factor:

| | calls |
|---|---|
| 2609.33415 (ψ = 0 only) | Õ(R√(H₀/ε) + R√H₁ log(Δ/ε)) |
| this result (any convex ψ, Q) | O((1 + R√(H₀/ε+H₁)) log(R²(H₀/ε+H₁)) log(Δ/ε)) |

The new instances are composite problems such as exponential losses with ℓ₁ penalties or constraints, where ∇f(x⋆) ≠ 0. Existing composite tools there either have curvature constants that blow up or pay an R G_ψ/ε smoothing term. The checked example shows that the gap constants can stay bounded while the gradient-norm constant L₁ grows as 1/δ. That gives a polynomial gain over the repository's composite (L₀,L₁) bound when ε ≫ δ² up to logarithms.

The comparison establishes this scope extension against the baselines I checked. Priority is less certain because this research group is releasing related preprints quickly, and I found no composite gap-curvature work. The claimable contribution is the first checked accelerated objective-gap guarantee for composite or constrained convex problems under total-gap curvature, using ordinary prox calls.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
