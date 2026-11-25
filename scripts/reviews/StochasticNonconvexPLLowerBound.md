# Novelty assessment: StochasticNonconvexPLLowerBound

[`result`](../../LongTails/Theorems/StochasticNonconvexPLLowerBound.lean) proves that every randomized algorithm (no `allowedAlgorithm` restriction) fails at every budget up to the stated one. "Fail" means E‖∇Φ_{1/(2ℓ)}(x̂)‖ > ε (or the quantity is non-integrable) on some admissible ℓ-smooth, μ-PŁ-in-y instance with an unbiased, σ²-bounded-variance, gradient-only IID oracle. The instance depends on the algorithm and the budget but not on the realized seed. Sources: [setup](../../LongTails/Setups/HighDimensionalStochasticNonconvexPL.lean), [general setup](../../LongTails/Setups/StochasticNonconvexPL.lean), [failure proof](../../LongTails/Proofs/NcPlFailure.lean). It is a lower bound, so no output algorithm is constructed.

**Proved necessary budget.** Parameters: ℓ is the joint Lipschitz constant of the gradients, μ the PŁ modulus in y, σ² the variance bound, ε the accuracy, and Δ ≥ 2Φ(x₀) − inf Φ − f(x₀,y₀) + ‖∇ₓf(x₀,y₀)‖²/ℓ the potential gap, with Φ = max_y f.

  T ≥ ⌊ℓ²Δ/(2⁹⁴με²)·(1 + ℓσ²/(2⁵⁹με²))⌋ = Ω( ℓ²Δ/(με²) + ℓ³Δσ²/(μ²ε⁴) ),

valid for ℓ ≥ 2⁴⁷μ, ℓΔ ≥ 2⁴⁷ε², and d ≥ 2⁹⁹(ℓ²Δ/(με²)·(1+ℓσ²/(με²)) + 1)(ℓΔ/ε²)²(ℓ/μ)³. This regime is nonempty: take ℓ = Δ = 1, μ = 2⁻⁴⁷, ε = 2⁻²⁴, and d large. The [companion upper bound](../../LongTails/Theorems/StochasticNonconvexPLUpperBound.lean) proves Smoothed-AGDA succeeds with 2⌈2⁴⁴·ℓ²Δ/(με²)·(1+ℓσ²/(με²))⌉ calls on the general class. The two budgets therefore match up to a universal constant, with no logarithmic factor, under the Moreau criterion.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Pan–Li, [arXiv:2608.26799](https://arxiv.org/abs/2608.26799) v1 (27 Aug 2026, preprint), Thm 3.2 (prior). Deterministic algorithms, NC-PŁ. | Ω(ℓ²Δ/(με²)) → Ω(ℓ²Δ/(με²) + ℓ³Δσ²/(μ²ε⁴)) | Adds the noise term. The necessary budget grows by a factor ≍ 1 + ℓσ²/(με²), which is a gain whenever σ² > με²/ℓ. | Deterministic algorithms → all randomized algorithms. Exact oracle → stochastic bounded-variance oracle. Their Sec. 6 lists the randomized extension as open. | Criterion ‖∇Φ‖ ≤ ε → E‖∇Φ_{1/(2ℓ)}‖ ≤ ε. The Moreau criterion is weaker, which makes the lower bound stronger; it still implies a bound for E‖∇Φ‖ ≤ ε/2 (prose argument only, not in Lean). | Their oracle also returns f values; this one returns gradients only. So at σ = 0 the result is not strictly stronger. It also needs d polynomial in κ, ℓΔ/ε², σ/ε, and huge constants. Δ is a potential gap ≥ the primal gap, so the instance class is smaller; for a lower bound that is stronger. |
| Wu et al., [arXiv:2610.00229](https://arxiv.org/abs/2610.00229) v2 (Oct 2026, preprint), Thm 3.4 (prior). Randomized algorithms, **NC-SC subclass only**. | Ω(√κ ℓΔ/ε² + κℓΔσ²/ε⁴ + κ²σ²/ε² + …) → Ω(κℓΔ/ε² + κ²ℓΔσ²/ε⁴), where κ = ℓ/μ | Noise term grows by a factor κ, and the deterministic term by √κ. Their κ²σ²/ε² term is dominated here because ℓΔ ≥ ε². | Their result covers strongly concave instances; this one covers PŁ instances, which are not concave. The instance classes are incomparable: theirs bounds the primal gap Φ(0) − inf Φ and ‖∇_y f(0,0)‖, while this one bounds the potential Δ. | Their criterion is P(‖∇Φ‖ ≤ ε) ≥ 2/3; this one uses the expected Moreau measure. | No transfer either way without a check of the initialization classes. Says nothing new about the strongly concave subclass. |
| Zhang–Wu–Yang, [arXiv:2609.35206](https://arxiv.org/abs/2609.35206) Thm 4.1/Cor 5.2, and Zhou, [arXiv:2609.30877](https://arxiv.org/abs/2609.30877) Thm 1 (prior, Sep 2026). Zero-respecting algorithms, **NC-SC only**. | Ω(κℓΔσ²/ε⁴) → Ω(κℓΔ/ε² + κ²ℓΔσ²/ε⁴) | Noise term grows by a factor κ. | Zero-respecting algorithms → arbitrary randomized algorithms. NC-SC → NC-PŁ. | Same Moreau-type criterion (Cor 5.2; Zhou Thm 1). | Zhou's class uses a bounded dual box and an initial gap G, so the classes differ. |

Ha, [arXiv:2610.07814](https://arxiv.org/abs/2610.07814) Thm 4.1, proves Ω(κ²ℓΔ/ε² + κ⁴ℓΔσ²/ε⁴) only for two-timescale SGDA. It is not a competitor for the problem class, but its Table 1 confirms the matching Smoothed-AGDA upper bound O(κℓΔ/ε² + κ²ℓΔσ²/ε⁴) (Yang–Orvieto–Lucchi–He, AISTATS 2022, [arXiv:2112.05604](https://arxiv.org/abs/2112.05604)). I did not re-read their theorem statement directly.

**Reduction check and proof ancestry.** The κ² noise term does not follow from any standard reduction I could find:
- Composing Pan–Li's chain with the probabilistic zero-chain masking of Arjevani et al. ([arXiv:1912.02365](https://arxiv.org/abs/1912.02365)) would at most plausibly cover zero-respecting algorithms. That composition is unpublished, and the note does not claim it.
- Handling arbitrary randomized algorithms needs the "robust saddle zero-chain" that Pan–Li leave open. Their dual block's gate vanishes only at 0, the block includes a −½‖y⁻‖² term, and its length scales are tied to the driver.
- The new mechanism here is a staggered-amplitude dual block with absolute gate thresholds that keeps PŁ with uniform modulus. It is combined with the inherited ingredients: Carmon et al.'s outer chain, the random-embedding hiding argument, and Bernoulli masking.

I did not audit the Lean proof's correctness. Running `grep` found no `sorry`, `admit` or `axiom` in the 21 `NcPl*` proof files, but I did not run the build or the comparator.

**Search coverage (25 Nov 2026).** Searched arXiv and the web for stochastic and randomized NC-PŁ and NC-SC lower bounds, read Pan–Li in full (Thms 3.1–3.2, Sec. 6) and the HTML of the three NC-SC papers and Ha. I found no prior or later all-algorithm stochastic NC-PŁ lower bound. The field moves fast, with many Aug–Oct 2026 preprints, so an unindexed concurrent result cannot be ruled out. Every comparator predates the 25 Nov 2026 commit `7b957e92`. The companion note's citations and claims agree with what I read.

## Conclusion

**Yes: this is the first lower bound I could find for stochastic nonconvex–PŁ minimax that holds for all randomized algorithms and captures the κ² noise term.** The decisive comparison is with Pan–Li's deterministic bound and the NC-SC stochastic bounds:

| | deterministic term | noise term | algorithm class |
|---|---|---|---|
| Best prior lower bounds | κℓΔ/ε² (Pan–Li) | κℓΔσ²/ε⁴ (NC-SC only) | deterministic / zero-respecting or NC-SC |
| This theorem | κℓΔ/ε² | κ²ℓΔσ²/ε⁴ | all randomized |
| Smoothed-AGDA upper bound | κℓΔ/ε² | κ²ℓΔσ²/ε⁴ | — |

The necessary noise cost rises by a factor κ = ℓ/μ. Together with the companion theorem, this pins the complexity at Θ(κℓΔ/ε² + κ²ℓΔσ²/ε⁴) under the Moreau criterion, which closes an open direction stated by Pan–Li.

The limits are real but secondary. The bound needs κ ≥ 2⁴⁷, ℓΔ ≥ 2⁴⁷ε², and a large polynomial dimension, and its constants are astronomically loose. The oracle returns gradients only, so the noiseless randomized case with function values stays open. Tightness for the ‖∇Φ‖ criterion covers only the two leading terms.

What can be claimed is a new, matching randomized lower bound for stochastic NC-PŁ optimization, built on a new robust dual block. Confidence is medium rather than high for three reasons: the area has many very recent preprints, a concurrent result may be unindexed, and I did not verify the Lean proof.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
