# Novelty assessment: RhoSmoothConvexLowerBound

[`result`](../../LongTails/Theorems/RhoSmoothConvexLowerBound.lean) is a lower bound. In the [setup](../../LongTails/Setups/RhoSmoothConvexFull.lean), fix any valid parameters, any randomized algorithm that queries exact gradients, and any budget b at most the stated one, including b = 0. Then some convex function f on ℝᵈ fails on that algorithm. Its admissibility conditions are taken from [RhoSmoothRadiusConvex](../../LongTails/Setups/RhoSmoothRadiusConvex.lean):

- f is differentiable with ‖∇²f(x)‖ ≤ L₀ + L₁‖∇f(x)‖^ρ;
- f has a minimizer x⋆ with ‖x⁰ − x⋆‖ ≤ R.

Failure means the expected gap 𝔼[f(x_out)] − f⋆ exceeds ε, or is not integrable. The hard instance may depend on the algorithm and on b, but not on the realized seed (assembled in [RhoSmoothLowerBranches](../../LongTails/Proofs/RhoSmoothLowerBranches.lean)).

**Necessary gradient calls.** The parameters are: L₀, L₁ > 0 are the smoothness constants, ρ ∈ (1,2] is the exponent, R is the initial distance, and ε is the accuracy.

N ≥ 2⁻³⁰ · ( √(L₀R²/ε) + (ρ−1)² R² L₀^{2−2/ρ} L₁^{2/ρ} ) − 1.

This needs ε ≤ L₀R²/16 and d ≥ 2⁴⁴(1 + R²L₀^{2−2/ρ}L₁^{2/ρ} + √(L₀R²/ε))⁶. Write Q := R²L₀^{2−2/ρ}L₁^{2/ρ} = (L₀R/G)², where G = (L₀/L₁)^{1/ρ} is the gradient norm at which L₁G^ρ = L₀.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nesterov's smooth lower bound (*Lectures on Convex Optimization*, 2018, Thm 2.1.7; repo [MollifiedSmoothLowerBound](../../LongTails/Proofs/MollifiedSmoothLowerBound.lean)). Special case: L₀-smooth functions lie in the class. | Ω(√(L₀R²/ε)) → Ω(√(L₀R²/ε) + (ρ−1)²Q) | Adds an ε-free term. Strict gain when (ρ−1)²Q ≫ √(L₀R²/ε). | None | None | Needs a much larger dimension, polynomial instead of linear. |
| Everest I, [arXiv:2610.21461](https://arxiv.org/abs/2610.21461) v2 (Oct/Nov 2026), Thm 4.10 for ρ = 1, transferred by the reduction below. | Ω(√(L₀R²/ε) + √Q/√log(2+√Q)) → Ω(√(L₀R²/ε) + (ρ−1)²Q) | √Q → (ρ−1)²Q. Strict gain when Q ≫ (ρ−1)⁻⁴ and (ρ−1)²Q ≫ √(L₀R²/ε). Example: ρ = 2, L₀ = L₁ = ε = 1 gives R → R². | None | Deterministic methods → randomized methods, expected accuracy. | Everest also allows function values (here: gradients only). Everest needs only d ≥ 2n. Weaker than √Q for Q < (ρ−1)⁻⁴, i.e. ρ near 1. |
| Repo [LogFreeGeneralizedSmoothLowerBound](../../LongTails/Theorems/LogFreeGeneralizedSmoothLowerBound.lean) (2026-11-18) for ρ = 1, transferred the same way. | Ω(√(L₀R²/ε) + √Q) → Ω(√(L₀R²/ε) + (ρ−1)²Q) | Same as the Everest row, without the log. | None | None (both randomized) | Same ρ↓1 loss. |

**Reduction.** By Young's inequality, L₀/2 + c·(L₀/G)·s ≤ L₀ + L₁s^ρ holds for all s ≥ 0 with a universal c > 0. So the ρ-class contains the affine (L₀/2, cL₀/G)-smooth class. Under this embedding, "L₁R" becomes about √Q, which is the strongest lower bound obtainable by transfer.

**Upper bounds.** The companion upper bound [RhoSmoothConvexUpperBound](../../LongTails/Theorems/RhoSmoothConvexUpperBound.lean) proves O(1 + √(L₀R²/ε) + Q). It uses an almost-sure criterion, which implies the expected-gap criterion used here. The two match up to (ρ−1)⁻² and constants. The upper bound in [Tyurin, arXiv:2508.06884](https://arxiv.org/abs/2508.06884) (v2 May 2026), §5.1 / Cor. 5.3, also needs the initial gap Δ. The instance here has an exponentially large Δ, so the known-Δ class is not settled.

**Why this is not a standard corollary.** Neither standard reduction gives the Q term:
- Nesterov's quadratics need curvature L₀ even where ∇f = 0.
- Smoothing a Lipschitz max-of-linear function puts curvature M²/μ near points with small gradient.

The new mechanism is a separable saturating dual with ψ′(r) = A(1 − (1+r/G)^{1−ρ}). Its slope is bounded only when ρ > 1, which gives an O(A)-scale chain with m ≍ (ρ−1)²Q links and no logarithm. A Young-type split keeps the localization wall polynomial.

**Proof ancestry.** These parts supply the scaffolding, not the Q exponent:
- Everest I §4: conjugate-of-polytope-regularizer chains, and Lemma 4.2's two-point smoothness transfer.
- Repo FinitePrefixExpectation and AdaptivePolynomialLocalization: randomized hiding and wall localization.

I did not run the build or the axiom audit.

**Search coverage.** On 2026-11-25 I searched arXiv and the web for lower bounds under ℓ-smoothness with ρ > 1. I read the theorem statements of Everest I/II and Tyurin's §1–3 and the summarized §5–6; their remaining appendices were not read verbatim. I checked the abstracts of [arXiv:2611.20318](https://arxiv.org/abs/2611.20318) (a different, generalized-Lipschitz class), [2611.29211](https://arxiv.org/abs/2611.29211) (GD upper bounds), and [2608.04884](https://arxiv.org/abs/2608.04884) ((H₀,H₁) upper bounds). None proves a ρ > 1 lower bound. Li et al. ([NeurIPS 2023](https://arxiv.org/abs/2306.01264)) give a lower bound only for GD. The companion note's citations agree with what I verified. The theorem was introduced in commit b37d9c82 on 2026-11-25, after all cited prior work.

## Conclusion

**Yes—this proves a quadratically larger lower bound than prior work implies for convex ρ-smooth minimization with ρ ∈ (1,2].** The strongest prior lower bound comes from embedding Everest I's affine (L₀,L₁) bound, or the repository's log-free randomized version:

| | necessary gradient calls |
|---|---|
| prior (by reduction) | Ω(√(L₀R²/ε) + R L₀^{1−1/ρ} L₁^{1/ρ}) |
| this result | Ω(√(L₀R²/ε) + (ρ−1)² R² L₀^{2−2/ρ} L₁^{2/ρ}) |

The ε-free term is squared. The total gain appears once (ρ−1)²R²L₀^{2−2/ρ}L₁^{2/ρ} exceeds both √(L₀R²/ε) and (ρ−1)⁻⁴. For example, with ρ = 2 and L₀ = L₁ = ε = 1, the bound grows from order R to order R².

The result loses to the reduction as ρ ↓ 1, where (ρ−1)² kills the new term. It also needs dimension polynomial in Q and allows gradient queries only. Its instance has a huge initial gap, so classes with a known gap remain open. Neither standard reduction gives the Q term, because both put large curvature near small gradients. The bounded-slope saturating dual, which exists only for ρ > 1, is a genuinely new ingredient.

I found no prior lower bound for ρ > 1 beyond √(L₀R²/ε). That supports priority, but some sections of the two closest papers were only read in summary.

What can be claimed: the first lower bound for ρ > 1 that captures the ε-free term. With the companion upper bound, it fixes the complexity of this radius-only class up to (ρ−1)⁻², with no log.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
