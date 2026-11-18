# Novelty assessment: KnownGapGeneralizedSmoothLowerBound

The [theorem](../../LongTails/Theorems/KnownGapGeneralizedSmoothLowerBound.lean) proves that on the [known-gap setup](../../LongTails/Setups/GeneralizedSmoothConvexKnownGapPolynomialDimension.lean) (convex C¹ f on ℝ^d with differentiable gradient satisfying ‖D∇f‖ ≤ L₀ + L₁‖∇f‖, exact-gradient oracle, a minimizer x* with ‖x₀ − x*‖ ≤ R and f(x₀) − f* ≤ Δ), every randomized algorithm, with no algorithm restriction (there is no output algorithm to name: this is a `NonConvergence` result), fails to reach expected gap ≤ ε on some algorithm- and budget-dependent instance whenever it uses at most the following number of gradient calls:

N ≥ ⌊max{ √(L₀R²/ε)/8192 , min{(L₁R·log(Δ/ε))^{2/3}, L₁R} / (2048·log(2+L₁R)) }⌋,

that is, **Ω(√(L₀R²/ε) + min{(L₁R log(Δ/ε))^{2/3}, L₁R}/log(2+L₁R))** calls are necessary. Here L₀, L₁ are the smoothness constants, R is the distance bound, Δ the known initial-gap bound, and ε the accuracy. The bound is proved only under these conditions: L₁R ≥ 2²⁰, 16ε ≤ L₀R², Δ ≥ ε·max{(2+L₁R)², √(L₀R²/ε)}, and d ≥ 2⁴⁶(1 + L₁R + √(L₀R²/ε))⁶. The regime is nonempty (`valid_nonempty`).

Write Λ = log(Δ/ε) and q = L₁R. Prior work: Rudomanov–Fomin–Gasnikov–Stonyakin, *Descending Everest I*, [arXiv 2610.21461](https://arxiv.org/abs/2610.21461) (v1 15 Oct 2026, v2 5 Nov 2026). Its lower bounds cover **deterministic** methods with an (f, ∇f) oracle in dimension 2n.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Everest I, Thm B.3 (lower bound on 𝒫_{4ε}, so it also holds on every 𝒫_Δ with Δ ≥ 4ε) | Ω(√(L₀R²/ε) + (q/log(2+L₁²ε/L₀))^{2/3}) → Ω(√(L₀R²/ε) + min{(qΛ)^{2/3}, q}/log(2+q)) | Gains a factor of order Λ^{2/3}/polylog(q) in the q-term when 4 log(2+q) ≲ Λ ≤ √q. At Λ = q^{1/3} the q-term goes from about q^{2/3} to about q^{8/9}/log q. | None (the class is the same) | Deterministic → randomized algorithms, with an expected-gap criterion | Gradient-only oracle, so algorithms that also query f are not covered. Needs dimension poly(q, √A), with A = L₀R²/ε, instead of 2n, and q ≥ 2²⁰. The band Δ < ε·max{(2+q)², √A} is excluded. |
| Everest I, Thm 4.8 (radius-only chain; instance gap ≥ 2ε·exp((n−1)√(log 4n / n)), Remark after 4.8). Substituting the largest n whose gap fits under Δ is my reduction, not a theorem in the paper. | About min{Λ²/log Λ, q/√log q} (the instance-gap upper estimate is unverified) → min{(qΛ)^{2/3}, q}/log(2+q) | Polynomial gain (q/Λ²)^{2/3} for q^{1/3} ≤ Λ ≤ √q. For Λ ≥ √q, both are of order q up to logarithms. | None | Deterministic → randomized | Same as the row above |
| Everest II, Thm 7.1, [arXiv 2611.04171](https://arxiv.org/abs/2611.04171) (v2 5 Nov 2026; finite sums with heterogeneity bound δ) | Has no Δ-dependence for Δ ≥ 2ε (Section 2) → Δ-dependent bound | Not comparable: the classes differ | Not comparable | Not comparable | Single function only |
| Repository [PolynomialDimensionGeneralizedSmoothLowerBound](../../LongTails/Theorems/PolynomialDimensionGeneralizedSmoothLowerBound.lean) (radius-only, randomized) | q/(4096 log(2+q)), whose instances have gap of order ε·e^{√m} → adds √A and the Δ-interpolation | Covers known-gap classes with Δ ≤ ε·e^{√(q/log q)} | Radius-only class → known-gap class | None | None beyond the regime conditions above |

**Gap to upper bounds.** Everest I Thm B.7(b) gives O(log(2+A+q)·[1 + √A + q^{2/3}·log^{2/3}(2Δ/ε)]) calls; I verified it only from the paper's summary table, not the theorem body. Everest I Thm 3.7 gives 5√A + 240(1+q)·log₂(64(1+q)) + 2. For Λ ≤ √q, the new lower bound is therefore within O(log(2+q)·log(2+A+q)) of the upper bound. For Λ > √q, it is within O(log²(2+q)) of Thm 3.7. The repository's [paired upper bound](../../LongTails/Theorems/KnownGapGeneralizedSmoothUpperBound.lean) counts log¹(Δ/ε), so it leaves an extra factor Λ^{1/3}.

**Reduction check and mechanism.** I found no substitution into Everest's theorems that gives (qΛ)^{2/3}. B.3 has no Λ, and the Thm 4.8 chain at admissible gap gives only about Λ². The new ingredient is a geometric-slope chain with a free per-link slope ratio e^h, chosen as h = Λ'/m. This trades total log-ratio against the radius budget and yields the exponent 2/3. A slope-gap margin then keeps the construction robust under mollification and randomized hiding. The proof ancestry is Everest's polytope-conjugate chain (§4.2, Lemma 4.5) and the repository's PR #168 randomization pipeline; I did not re-derive the Lean proof, and I ran no build or axiom audit.

**Search coverage.** On 2026-11-17 I searched arXiv and the web for convex (L₀,L₁) lower bounds that depend on the gap: Everest I/II, Lobanov [arXiv 2608.04884](https://arxiv.org/abs/2608.04884) (no lower bound), Vankov et al. and Tyurin as cited by Everest II, and nonconvex works such as [arXiv 2610.21692](https://arxiv.org/abs/2610.21692). I found no Δ-dependent lower bound. Everest I §5 states that "a matching lower bound in terms of the dependence on Δ is unknown." I verified Everest II §8.1 only through a summary. The result was introduced on 2026-11-17 (commit e0cc31dc), after both Everest preprints. The companion note's claims agree with what I checked, except that its quotation of B.7(b) rests on my table-level check.

## Conclusion

**Yes: this proves a new, essentially tight lower bound on how the complexity depends on the known initial gap Δ.** Before it, the strongest result was Everest I (Thm B.3, plus Thm 4.8 at admissible gap), and it gave no lower bound that grows with log(Δ/ε) beyond about log²(Δ/ε).

| Bound on the q-term (q = L₁R, Λ = log(Δ/ε)) | Order |
|---|---|
| Prior lower bound (deterministic) | max{q^{2/3}, Λ²} up to logarithms |
| New lower bound (randomized) | min{(qΛ)^{2/3}, q}/log(2+q) |
| Upper bound (Everest B.7(b) / Thm 3.7) | min{q^{2/3}Λ^{2/3}, q} up to logarithms |

The gain is polynomial when log q ≪ Λ ≪ √q. For example, at Λ = q^{1/3} the q-term rises from about q^{2/3} to about q^{8/9}. Upper and lower bounds then agree up to polylogarithmic factors across the valid regime. This answers the open question stated in Everest I §5.

Some limitations remain. The oracle is gradient-only, so algorithms that also query function values are not covered, while randomized algorithms are newly covered. The bound needs polynomial dimension and L₁R ≥ 2²⁰, and it excludes Δ < ε·max{(L₁R)², √(L₀R²/ε)}. In that excluded band, B.3 already gives a bound tight up to logarithms in the deterministic model. My search found no prior or concurrent Δ-dependent lower bound, but that does not prove priority, given how recent the area is.

What can be claimed: the first lower bound that captures the (L₁R·log(Δ/ε))^{2/3} dependence for convex (L₀,L₁)-smooth minimization with known gap, matching the known upper bound up to logarithms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
