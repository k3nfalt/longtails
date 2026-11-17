# HighDimensionalStrongQuasarLowerBound: randomized Ω(γ⁻¹√κ·log) lower bound for strongly quasar-convex minimization

[`result`](../../LongTails/Theorems/HighDimensionalStrongQuasarLowerBound.lean) proves the following, with setup [`HighDimensionalStrongQuasar`](../../LongTails/Setups/HighDimensionalStrongQuasar.lean) and hard instance in [`StrongQuasarChainLowerBound`](../../LongTails/Proofs/StrongQuasarChainLowerBound.lean). Take any randomized algorithm with exact-gradient access (adaptive queries, arbitrary output, no span restriction) and any budget `b ≤ ⌊√κ/(8000γ)⌋·⌊log₂⌊Δ/(1000γ√κε)⌋⌋/2`, including `b = 0`. Then some L-smooth, (γ,μ)-strongly quasar-convex `f` on ℝᵈ with `f(x₀) − f⋆ ≤ Δ` makes `𝔼[f(output)] − f⋆ > ε` (the expectation is over the algorithm's seed).

**Necessary budget.** Write κ = L/μ, where L is the smoothness, μ the strong-quasar modulus, γ ∈ (0,1] the quasar parameter, Δ the initial gap and ε the expected-gap accuracy. The theorem gives

  **Ω( γ⁻¹ √(L/μ) · log(Δ/(γ√(L/μ) ε)) )** gradient calls.

This holds on the domain `γ ≤ 1/256`, `L ≥ 870400μ`, `γ²L ≥ 4μ`, `Δ ≥ 1000γ√κε` and `d ≥ (√κ/γ)⁵(Δ/(1000γ√κε))³`. The bound is nonvacuous once `Δ ≥ 2000γ√κε`; the first factor is always ≥ 29 on this domain. The regime is nonempty: take L = 10⁷, μ = 1, γ = 1/256, Δ = 1, ε = 10⁻¹⁰ and d ≈ 2·10⁵⁶. The known upper bound in the same setup ([`HighDimensionalStrongQuasarUpperBound`](../../LongTails/Theorems/HighDimensionalStrongQuasarUpperBound.lean)) is `⌈32√κ/γ⌉·⌈log₂(1+2Δ/(γε))⌉`. The two bounds match up to a constant when ε ≤ Δ/(10⁶γκ), and up to a factor O(log κ) otherwise.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Hinder–Sidford–Sohoni, [arXiv 1906.11985 v3](https://arxiv.org/abs/1906.11985) (COLT 2020), Remark 4 and its proof in App. E.3. Deterministic methods. | Proved: Ω(max{γ⁻¹√κ, γ^{-1/2}√κ·log(Δ/ε)}) → Ω(γ⁻¹√κ·log(Δ/(γ√κε))). The Remark *states* the product, but its proof gives only γ^{-1/2}√κ·log, via the reduction "SQC quadratic ⇒ (γμ/2)-strongly convex". | The necessary budget is larger by a factor Θ(min{γ^{-1/2}, log(Δ/(γε))}) when ε ≤ Δ/(10⁶γκ). Example: if γ = κ^{-1/4} and ε = Δκ^{-c} with c ≥ 2, the gain is Θ(min{κ^{1/8}, c·log κ}). Smaller gains hold when ε > Δ/(10⁶γκ). | Deterministic algorithms → all randomized algorithms. Same objective class. | None (same expected/deterministic ε-gap criterion) | Requires γ ≤ 1/256, γ√κ ≥ 2, κ ≥ 870400, and dimension polynomial in √κ/γ and Δ/ε (exponential in the number of e-folds). Constants are about 10⁶ looser. |
| Randomized lower bounds for (γμ)-strongly convex functions, which are a subclass of SQC with condition number κ/γ. E.g. Woodworth–Srebro, [NeurIPS 2016](https://arxiv.org/abs/1605.08003) (theorem number not re-verified). | Ω(γ^{-1/2}√κ·log(Δ/ε)) → Ω(γ⁻¹√κ·log(Δ/(γ√κε))) | Gain factor Θ(γ^{-1/2}) when ε ≤ Δ/(10⁶γκ). No randomized exact-gradient γ⁻¹√κ term was found in the literature at all. | Same class; the γ⁻¹ factor is now captured for randomized methods. | None | Same domain and dimension restrictions as above. Needs large d, as is usual for randomized chain bounds. |

**Reduction check.** Lower bounds pass from subclasses to superclasses, so strongly convex quadratics cannot exceed γ^{-1/2}√κ. HSS's regularization of their quasar chain produces a single accuracy scale: it gives γ⁻¹√κ, but no log factor. The PL lower bound of Yue–Fang–Lin (COLT 2023) concerns a larger class, so it does not transfer to SQC. I found no substitution or composition that yields the product.

**What is new in the proof.** The mechanism is a geometric chain with exact KKT conditions, a masked quadratic reward and a sequence-level strong-quasar inequality (`Regime.chain_nonneg`). This construction keeps strong quasar-convexity with chain length ≍ √κ/γ per e-fold, and that is the genuinely new ingredient. Coordinate hiding against randomized algorithms is standard, in the style of Woodworth–Srebro and Carmon et al.; the localization machinery is reused from the repository.

**Search coverage.** Searched 2026-11-17 (UTC): arXiv, PMLR, OpenReview and the web, for quasar or strongly quasar-convex lower bounds 2019–2026.
- I read HSS v3 Thm 1, Thm 3, Remarks 3–4 and the App. E.3 proof.
- Saad–Lee–Orabona ([arXiv 2502.14060 v2](https://arxiv.org/abs/2502.14060), Thm 3.2) give a randomized lower bound σ²/(μτ²T) that vanishes at σ = 0, so it does not cover this setting.
- Upper bounds come from HSS Thm 1 (with an extra log(κ/γ) factor and function-value queries) and from [Wang–Wibisono, ICLR 2023](https://openreview.net/pdf?id=yYbhKqdi7Hz).
- NeurIPS 2026 OpenReview pages were not checked. The companion note's citations agree with what I verified. The note does not mention that HSS's Remark 4 *statement* already asserts the deterministic product.

## Conclusion

**Yes: this proves a larger necessary complexity than any previously proved lower bound for smooth strongly quasar-convex minimization, and it covers randomized algorithms.**

The strongest prior proved bound is Hinder–Sidford–Sohoni's, for deterministic methods only:

| | Necessary gradient calls |
|---|---|
| Before (proved) | max{γ⁻¹√κ, γ^{-1/2}√κ·log(Δ/ε)} |
| This result (randomized) | γ⁻¹√κ·log(Δ/(γ√κε)) |
| Known upper bound | γ⁻¹√κ·log(Δ/(γε)) |

When ε ≤ Δ/(10⁶γκ), the lower bound matches the upper bound up to a constant. It improves the proved bound by a factor of about min{γ^{-1/2}, log(Δ/(γε))}. For larger ε, a gap of O(log κ) remains.

The gain is limited to small γ (≤ 1/256, but with γ√κ ≥ 2) and to very high dimension, polynomial in √κ/γ and Δ/ε. Both are typical artifacts of hiding constructions and do not change the rate claim. On priority, HSS's Remark 4 states the deterministic product without proving it; the new theorem supplies the first proof I found, and extends it to randomized algorithms. The search found no competing proof, but that is not proof that none exists.

The claimable contribution is the first verified proof that the γ⁻¹√κ·log(1/ε) accelerated rate is optimal (in this regime) for randomized first-order methods. It rests on a new chain construction that preserves strong quasar-convexity.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
