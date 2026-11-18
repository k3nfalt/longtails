# Novelty assessment: SphericalPreferenceLowerBound

[`result`](../../LongTails/Theorems/SphericalPreferenceLowerBound.lean) proves `NonConvergence` for the [spherical random-utility setup](../../LongTails/Setups/SphericalRandomUtility.lean): for `d ≥ 2`, `R, B > 0`, `0 < ε ≤ BR/16`, every randomized adaptive algorithm making `b ≤ ⌊d(BR/ε)²/524288⌋` binary comparisons fails, on some convex instance chosen before the seed is drawn, to get `∫ f(output) − f(x*) ≤ ε` on the radius-`R` ball. The instance is one of the [hypercube instances](../../LongTails/Proofs/SphericalPreferenceHypercube.lean): a linear `f_v` of slope `8ε/R` plus a two-component spherical Gaussian taste mixture.

**Proved necessary budget:** `N ≥ ⌊d B² R² / (524288 ε²)⌋ = Ω(d B²R²/ε²)`. Here `d` is the dimension, `R` the ball radius, `B` the median Lipschitz bound of a respondent's utility `f + ⟨Z,·⟩`, and `ε` the expected objective accuracy. The cost unit is one comparison, i.e. one fresh respondent. The bound is vacuous (budget 0) unless `ε ≤ BR√d/724`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kovalev–Stonyakin–Gasnikov, [arXiv:2611.19611 v1](https://arxiv.org/abs/2611.19611) (14 Nov 2026, preprint), Thm 2(b), μ=0, `r=R`, `M=B/2`, `σ=B/(4√d)` | `Ω(dB²R²/ε²)`, explicitly `N ≥ dB²R²/(160000ε²)` for `ε < BR/200` → `N ≥ ⌊dB²R²/(524288ε²)⌋` for `ε ≤ BR/16` | None: same order. The prior constant is about 3.3× larger where both apply. The new result additionally covers the constant-accuracy band `BR/200 ≤ ε ≤ BR/16`, where it gives Ω(d) comparisons once `d ≳ 2000` | None. The prior Gaussian probit instances already lie in this class (see below) | None. Both are expected-gap bounds against randomized adaptive algorithms | The proof here is formal and handles the repository's tie rule; the prior result has a fair-coin tie, which carries no information either way |
| Repository upper bound [SphericalPreferenceDescent](../../LongTails/Theorems/SphericalPreferenceDescent.lean) (same commit) | Upper `⌈d(672BR/ε)²⌉` vs lower `⌊d(BR/ε)²/524288⌋` | Matching order `Θ(dB²R²/ε²)`. The constant gap is ≈2.4·10¹¹ | Same setup, oracle and criterion | — | Optimality holds only for the single-envelope class, not for low-noise subclasses |

**Reduction check.** Kovalev et al.'s oracle (their eqs. (3)–(4)) is `f(X)+⟨ξ,X⟩` with `ξ ~ N(0,σ²I_d)`. That is exactly this setup's sample utility, with a spherical law. Take `M = B/2` and `σ = B/(4√d)`. Then `E‖ξ‖² = B²/16`, so by Markov `P(‖ξ‖ ≤ B/2) ≥ 3/4`. Every `M`-Lipschitz convex `f` therefore gives a `B`-Lipschitz utility with probability ≥ 1/2, so all of their instances are admissible here. Their bound `(1/100)·min{MR, dσR/√N} > ε` is then equivalent to `ε < BR/200` and `N < dB²R²/(160000ε²)`.

An infimum-over-algorithms risk bound gives, for each algorithm, an instance whose error exceeds ε. That is the repository's `NonConvergence` quantifier at every `b ≤ N`, including `b = 0`. So the order follows by substitution into a prior theorem. The new ingredients are minor technical choices: the two-component mixture keeps answer probabilities ≥ 1/16, and the Hellinger/hypercube transcript argument is the standard Assouad-type mechanism. I verified the statement of their Theorem 2. Their Appendix B.2 construction was not fully read, but the reduction uses only the theorem statement.

**Search coverage (18 Nov 2026).** Searches covered arXiv/proceedings for comparison-oracle, dueling, and stochastic-order-oracle convex optimization lower bounds. I read the abstract page and Theorem 2 of arXiv:2611.19611. Jamieson–Nowak–Recht ([NeurIPS 2012, arXiv:1209.2434](https://arxiv.org/abs/1209.2434)) and Saha–Koren–Mansour ("Dueling Convex Optimization", ICML 2021) use unnormalized-gap or flip-probability links. Their hard instances do not obviously fit this random-linear-utility model, and their theorems were not checked in detail. Chronology: Kovalev et al. v1 (14 Nov 2026) predates the repository commit `3cafd15f` (18 Nov 2026 UTC) introducing this theorem. The companion note acknowledges this prior result and is consistent with the Lean statement.

## Conclusion

**No: the lower bound's order is already known; this is a formal re-proof of a direct corollary.**

The closest baseline is Kovalev, Stonyakin and Gasnikov's Theorem 2(b), posted four days before this theorem was introduced. Their Gaussian random-coefficient probit model is a subclass of this setup. Substituting `M = B/2` and `σ = B/(4√d)` gives:

| | Necessary comparisons | Regime |
|---|---|---|
| Kovalev et al. (prior) | `dB²R²/(160000 ε²)` | `ε < BR/200` |
| This theorem | `⌊dB²R²/(524288 ε²)⌋` | `ε ≤ BR/16`, `d ≥ 2` |

Where both apply, the prior bound is about 3.3 times stronger. The only extra coverage is the constant-accuracy band `BR/200 ≤ ε ≤ BR/16`. There the new bound says roughly `d` comparisons are needed, and only when `d` is in the thousands. That is a constant-factor matter, not a new rate.

What stands is this: together with the companion upper bound, the result pins down the order `Θ(dB²R²/ε²)` for the median-envelope class, with an adaptive, randomized, seed-independent proof. The lower-bound half of that pairing was already available, and the proof uses a standard hypercube/Hellinger mechanism. The claimable contribution is a machine-checked proof of a known lower-bound order in the repository's exact model. The substantive novelty of the pair lies in the upper bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
