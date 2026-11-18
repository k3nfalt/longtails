# Novelty assessment: LogFreeGeneralizedSmoothLowerBound

The [theorem](../../LongTails/Theorems/LogFreeGeneralizedSmoothLowerBound.lean) is a `NonConvergence` statement for the [GeneralizedSmoothConvexFull setup](../../LongTails/Setups/GeneralizedSmoothConvexFull.lean). It covers every randomized algorithm with exact gradient queries anywhere in ℝᵈ. Every such algorithm, run for any budget b ≤ ⌊(√(L₀R²/ε) + L₁R)/2²⁶⌋, fails on some convex function with ‖∇²f(x)‖ ≤ L₀ + L₁‖∇f(x)‖ and some minimizer within R of x⁰. The criterion is expected accuracy: E[f(x̂)] − f* > ε. The function may depend on the algorithm and on b, but not on the random seed. There is no algorithm module, because lower bounds have none.

**Proved necessary budget:** Ω(√(L₀R²/ε) + L₁R) gradient calls. Here L₀, L₁ ≥ 0 are the generalized-smoothness constants, R is the distance from x⁰ to a minimizer, and ε is the target accuracy. This holds for every L₀, R, ε > 0 and L₁ ≥ 0 with ε ≤ L₀R²/16 and dimension d ≥ 2⁴⁴(1 + L₁R + √(L₀R²/ε))⁵. No bound on the initial gap is assumed. The proof splits into three cases ([TailEntropyBudget](../../LongTails/Proofs/TailEntropyBudget.lean)):
- b = 0.
- s ≥ q, where s = √(L₀R²/ε) and q = L₁R: Nesterov's chain with mollification.
- q > s with q ≥ 2²⁴: a new chain built on a "tail-ratio entropy" ([TailEntropyChainLowerBound](../../LongTails/Proofs/TailEntropyChainLowerBound.lean)).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, [Descending Everest I](https://arxiv.org/abs/2610.21461), Thm 4.10 (preprint; v1 15 Oct 2026, v2 5 Nov 2026; prior) | 1+N ≥ (1 + √(L₀R²/ε) + L₁R/√log(2+L₁R))/29 → b ≥ ⌊(√(L₀R²/ε)+L₁R)/2²⁶⌋ | Larger necessary budget by a factor √log(2+L₁R) when L₁R ≳ √(L₀R²/ε). Same order when √(L₀R²/ε) ≥ L₁R. The gain is in order only: with the explicit constants (1/29 vs 2⁻²⁶), the new bound is numerically larger only for astronomically large L₁R. | Deterministic algorithms → randomized algorithms. Deterministic accuracy → expected accuracy (a weaker success criterion, so a stronger lower bound). | None | Gradient-only oracle, whereas Everest also allows function values (the value+gradient extension is only argued in the companion note, not formalized). Dimension d = 2n ≈ L₁R → d ≳ (1+L₁R+√(L₀R²/ε))⁵. Neither statement contains the other. |
| Repository [FullGeneralizedSmoothConvexLowerBound](../../LongTails/Theorems/FullGeneralizedSmoothConvexLowerBound.lean) (14 Nov 2026; same setup) | ⌊(√(L₀R²/ε) + L₁R/log(2+L₁R))/2²³⌋ → ⌊(√(L₀R²/ε)+L₁R)/2²⁶⌋ | Factor log(2+L₁R) on the L₁R term. With the explicit constants it is larger once log(2+L₁R) > 8. | None (identical setup) | None | None |

Gap to upper bounds: Everest I Thm 3.7 and the repository's [RadiusFreeGeneralizedAccelerated](../../LongTails/Theorems/RadiusFreeGeneralizedAccelerated.lean) both give O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R)) calls. The remaining gap is log(2+L₁R), down from Everest's stated log^{3/2}(2+L₁R) (Section 5). At L₁ = 0 the result is the classical randomized Ω(√(L₀R²/ε)) bound and is not new.

**Reduction check and proof ancestry.** Retuning Everest's chain does not give this result. Everest's Section 5 attributes the lost √log to "the choice of the slopes and shifts of the chain". The obstacle is the margin ≳ log n/L₁ that the separable dual regularizer forces. The new mechanism is the non-separable regularizer Σ z_m log(z_m/T_m) with tail sums T_m = Σ_{i≥m} z_i. It has two parts:
- a curvature inequality that uses max_i z_i;
- a mass-transfer argument that needs only a cumulative margin.

Together these let n ≈ L₁R chain links fit. The proof inherits two pieces:
- From Everest I: the conjugate-chain architecture and Lemma 4.2, which turns dual strong convexity into (L₀,L₁)-smoothness.
- From the repository: the randomized-embedding pipeline from the earlier lower-bound PRs, a random-embedding technique of the kind used by Woodworth–Srebro (2016); it supplies the extension to randomized algorithms.

[Descending Everest II](https://arxiv.org/abs/2611.04171), Thm 7.1, is a randomized lower bound, but only for sums of at least two components with a component oracle. It loses log²N₀ and gives no single-function bound.

**Search coverage (18 Nov 2026).**
- *Searched:* arXiv and Google-style searches for lower bounds on (L₀,L₁) convex and generalized-smooth optimization.
- *Read:* Everest I v2, Sections 1–5 and App. A, plus the Thm 4.10 and Thm 3.7 statements. Everest II v2, Thm 7.1. Tyurin [arXiv:2508.06884](https://arxiv.org/abs/2508.06884) v2, which has only a Nesterov-type Ω(√(L₀R²/ε)) remark.
- *Not covered:* Everest I Appendices B–D were not read verbatim.
- *Not run:* I did not build the proof or audit its axioms.
- *Companion note discrepancy:* the note says Everest lists the lost √log as an open question. Section 5 actually poses only the combined log^{3/2} gap, while saying where the √log is lost.
- *Chronology:* the result was introduced in commit f7a81b19 on 18 Nov 2026. Both Everest papers are earlier, unrefereed preprints.

**Conclusion**

**Yes: this is a strictly larger lower bound, removing the logarithm from the L₁R term.** The strongest baseline is Descending Everest I, Theorem 4.10, for deterministic methods on the same radius-only convex (L₀,L₁)-smooth class:

| | necessary calls |
|---|---|
| Everest I (deterministic, values+gradients) | Ω(√(L₀R²/ε) + L₁R/√log(2+L₁R)) |
| This theorem (randomized, gradients) | Ω(√(L₀R²/ε) + L₁R) |
| Best upper bound | O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R)) |

The gain is a factor √log(2+L₁R), present when L₁R ≳ √(L₀R²/ε). Combined with the known upper bound, the oracle complexity is now settled up to a single log(2+L₁R) factor, which appears only in the upper bound. The gain is not a reparametrization: it comes from a new non-separable dual regularizer that removes exactly the obstacle Everest identifies.

There are tradeoffs. The formal theorem covers gradient-only oracles, so Everest's value+gradient model is reached only by an unformalized remark. It also needs polynomially large dimension, and its constants are very loose, so the gain is in order of magnitude only. My search found no earlier log-free bound. However, the field is moving fast and consists of preprints, so priority is supported, not proven.

What can be claimed: the first (as far as I found) log-free Ω(√(L₀R²/ε) + L₁R) lower bound for convex (L₀,L₁)-smooth minimization with only a radius bound, valid for randomized gradient methods.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
