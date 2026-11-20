# Novelty assessment: SharpLipschitzConvexRestartedSubgradient

The [theorem](../../LongTails/Theorems/SharpLipschitzConvexRestartedSubgradient.lean) shows that the [restarted subgradient method](../../LongTails/Algorithms/RestartedSubgradient.lean) returns a phase average x̂ with f(x̂) − f⋆ ≤ ε. This holds deterministically, so the expected gap is also at most ε. The method uses phases of length T = ⌈4L²/μ²⌉, each starting from the previous phase's average with step (D/2ᵏ)/(L√T). The guarantee covers every convex, L‑Lipschitz, globally μ‑weakly sharp f : ℝᵈ → ℝ with a minimizer within D of x₀, and every subgradient selection ([setup](../../LongTails/Setups/SharpLipschitzConvex.lean)).

**Complexity.** The parameters are: L, the Lipschitz constant; μ ≤ L, the sharpness modulus, meaning f − f⋆ ≥ μ·dist(·, argmin f); D, a bound on the initial distance to a minimizer; and ε, the target accuracy. The proved budget is ⌈4L²/μ²⌉·(⌈log₂⌈μD/ε⌉⌉ + 1). In O-form this is

  **O((L/μ)² · log(2 + μD/ε))** value-and-subgradient calls.

At least ⌈4L²/μ²⌉ calls are charged even when ε ≥ LD, where x₀ already succeeds.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Yang–Lin, RSG, [JMLR 19 (2018)](https://www.jmlr.org/papers/v19/17-016.html), [arXiv v14](https://arxiv.org/abs/1512.03107), Cor. 7 (θ=1) / Cor. 9. Requires a known ε₀ ≥ f(x₀) − f⋆; take ε₀ = LD, which is admissible because f(x₀) − f⋆ ≤ LD. | O((L/μ)² log(2 + LD/ε)) → O((L/μ)² log(2 + μD/ε)) | Saves an additive O((L/μ)² log(L/μ)). This is a factor up to log(L/μ) when ε ≥ μ²D/L, and the same order when ε ≤ μ²D/L. Given ε₀ instead of D, setting D = ε₀/μ recovers RSG's log(ε₀/ε). | None. RSG needs only a local error bound on the ε-sublevel set, a broader class. | None. Both output a phase average with a deterministic objective gap. | Global sharpness is required. RSG uses 0 calls when ε₀ ≤ ε, whereas this budget always charges ⌈4κ²⌉ calls (κ = L/μ). The gain is just a distance-based first step instead of a gap-based one. |
| Wang, [arXiv 2512.13863 v1](https://arxiv.org/abs/2512.13863) (Dec 2025, preprint), Thm. 1: decaying/GeomGD steps. This row is restricted to μ ≤ L/√2. | Distance (1−μ²/L²)^{n/2}D; with gap ≤ L·dist this is O((L/μ)² log(2 + LD/ε)) → O((L/μ)² log(2 + μD/ε)) | Same additive log(L/μ) saving in the same regime. Composing GeomGD with one final averaged phase of ⌈4κ²⌉ steps already gives the log(μD/ε) form. | None. Wang's error bound is required only within distance D of argmin, a broader class. | Last iterate (Wang) → phase average (here). | Wang's Polyak variant needs f⋆. |
| Wang, same paper, Thm. 2 / Cor. 1: lower bound for span methods | N_ε ≈ 2(L/μ)² log(μD/ε) necessary for span methods | Matches up to constants for span methods (an upper vs. lower bound, not a competing algorithm). | — | — | Lower bound only. The repository's companion [lower bound](../../LongTails/Theorems/SharpLipschitzConvexLowerBound.lean) extends it to general methods; that is a separate result. |

**Reductions and proof ancestry.** The result is a direct composition of standard pieces: the averaged subgradient bound (Lemma 2 in Yang–Lin; Zinkevich/Nesterov) gives the per-phase gap, and sharpness halves the distance after each phase. This is the restart scheme of Nemirovski–Nesterov (1985) and Yang–Lin with distance-based rather than gap-based phase steps. No new mechanism is involved.

**Search coverage.** Searched on 2026-11-20. I read the Yang–Lin arXiv v14 theorem statements (Assumption 1, Thm. 3, Cor. 7, Cor. 9) and the Wang v1 HTML (class definition, Thm. 1, Thm. 2, Cor. 1). Goffin (1977), Polyak (1969), Davis et al. ([JOTA 2018](https://arxiv.org/abs/1803.02461)) and Johnstone–Moulin were not read; they are cited only via Wang and the note. The theorem was introduced in commit c3a26ec9 (2026-11-20), after all the cited work. The companion note itself correctly says "not a new rate" and claims no novelty; I found no discrepancy with the Lean statement.

**Conclusion**

**No: this is a formalization of the classical restarted-subgradient rate, not a new guarantee.**

The strongest baseline is Yang–Lin's RSG (JMLR 2018, Cor. 7 with θ = 1). With its required initial-gap bound set to ε₀ = LD, RSG gives:

| | calls for f(x̂) − f⋆ ≤ ε |
|---|---|
| RSG (ε₀ = LD) | O((L/μ)² log(2 + LD/ε)) |
| This theorem | O((L/μ)² log(2 + μD/ε)) |

The only difference is an additive (L/μ)² log(L/μ). It matters only at low accuracy (ε ≥ μ²D/L) and comes from choosing the first phase's step from D instead of from ε₀. If one knows ε₀ instead of D, RSG already gives log(ε₀/ε), and so does this theorem with D = ε₀/μ. Both methods output a phase average with deterministic accuracy. RSG and Wang's analysis also cover broader local error-bound classes, whereas this theorem needs global sharpness. It also always charges about 4(L/μ)² calls, even when no work is needed.

The value of this file is as the matching upper half of the repository's tight pair. Wang's span-method lower bound (Cor. 1) already shows this rate is optimal among subgradient-span methods, and the companion lower-bound theorem is what would carry any novelty. What can be claimed here is a faithful formal proof of a known rate under the same oracle and criterion as that lower bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
