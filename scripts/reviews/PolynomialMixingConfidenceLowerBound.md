# Novelty assessment: PolynomialMixingConfidenceLowerBound

The [theorem](../../LongTails/Theorems/PolynomialMixingConfidenceLowerBound.lean) proves the following in the [setup](../../LongTails/Setups/PolynomialMixingSubgradient.lean). Fix a valid parameter choice, any randomized adaptive algorithm, and any call count up to the budget, including zero. Some admissible convex objective on the radius-`R` ball, with a stationary oracle stream, then makes the measurable output miss `P(f(x̂) − f* ≤ ε) ≥ 1 − δ`. The stream has past–future β-mixing coefficient at most `(1+t/τ)^(−β)`, and the replies' stationary mean is a supporting subgradient with raw moment `E‖g(x,Z)‖^p ≤ G^p`. The setup imposes no `allowedAlgorithm` restriction. The lower bound has no algorithm of its own; the [hard instances](../../LongTails/Proofs/PolynomialMixingHardInstance.lean) are one-coordinate linear objectives with query-independent replies.

**Proved necessary budget.** Write `a = p/(p−1)`, where `p` is the moment order, `β` the mixing exponent, `τ` the mixing time scale, `G` the moment scale, `R` the ball radius, `ε` the accuracy and `δ` the failure probability. Then

`N ≥ ⌊ τ/(8(1+2β)) · [ (GR/(8ε))^(a(1+1/β)) · log(1/(4δ)) + (16δ)^(−1/β) ] ⌋`.

This holds for `d ≥ 1`, `1 < p ≤ 2`, `β > 0`, `τ ≥ 1`, `0 < ε ≤ GR/8` and `0 < δ ≤ 1/32`, so the regime is nonempty. The [companion upper bound](../../LongTails/Theorems/PolynomialMixingConfidenceUpperBound.lean), from the same commit, needs `⌈τ(32L)²[(2²⁴GR/ε)^(a(1+1/β)) + ((32L)²/δ)^(1/β)]⌉` calls, where `L = log(8/δ)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository, earlier: [PolynomialMixingHeavyTailedConvexLowerBound](../../LongTails/Theorems/PolynomialMixingHeavyTailedConvexLowerBound.lean). Stationary Markov chain with average-TV mixing, which is the β-mixing coefficient for a stationary Markov chain. Smooth convex objectives, centered α-moment `σ`. Criterion: expected gap. | `(τ/β)·((σR/ε)^α/2^(4α−1))^((1+1/β)/(α−1))` → `τ/(1+β)·[(GR/ε)^(a(1+1/β))·log(1/δ) + δ^(−1/β)]`, with constants depending on `p` and `β` | The accuracy exponent is unchanged; the new parts are a `log(1/δ)` factor and an additive `τδ^(−1/β)`. Polynomially larger when `δ^(−1) ≳ (GR/ε)^(a(β+1))`. Example (`p=2`, `β=τ=G=R=1`, `ε=1/8`, `δ=2⁻²⁰`): 2731 vs 64 at `σ=G`. | Incomparable classes: (smooth, centered moment, Markov) vs (supporting-subgradient, raw moment, any stationary β-mixing stream) | Expected gap → probability `1−δ`. These criteria do not convert into each other without extra steps. | Linear hard instances only. Constants shrink like `8^(−a(1+1/β))/(1+β)`. |
| Sarkar–Chakrabartty–Aggarwal, [arXiv:2606.26316](https://arxiv.org/abs/2606.26316) v1 (24 Jun 2026, preprint), Thm 4 (heavy-tailed, any estimator). Thm 2 / Cor. 2 is for SGD only. | Constant-confidence `n ≳ t_mix·(σ²/ε)^(p/(2(p−1)))` for PL quadratics under uniformly geometric mixing → bound above | Not comparable: different objective class and accuracy scaling. Their bounds contain no `δ`. | Geometric uniform mixing → polynomial β-mixing envelope | Constant probability → every `δ ≤ 1/32` | None of their PL/smooth structure. Applies to the ball-constrained subgradient model only. |
| Companion upper bound (same commit; a gap check, not prior work) | `τL²[(2²⁴GR/ε)^(a(1+1/β)) + (L²/δ)^(1/β)]` vs the lower bound | The polynomial exponents of `ε`, `δ` and `τ` match for fixed `p, β`. The remaining gap is `log(1/δ)` on the accuracy term, `L^(2+2/β)` on the confidence term, and constants exponential in `a(1+1/β)`. | Same setup | Same criterion | Exact logarithmic dependence and uniformity as `p→1` or `β→0` remain open |

**Reduction check / mechanism.** The accuracy term reuses the earlier repository idea: a rare, persistent "informative" state whose replies are scaled by `G·b^(−1/p)`. Turning that into a high-probability bound by requiring a silent stretch with probability above `2δ` is standard two-point testing. The `δ^(−1/β)` term is new in the compared lower bounds. It comes from an elementary "information blackout" construction: overlapping Bernoulli windows whose β-mixing coefficient stays inside the envelope, while an event of mass `≈8δ` suppresses all information for `≈τδ^(−1/β)` steps. This matches the block-length requirement `β(q) ≲ δ` that dependent-block upper bounds such as Lerasle–Oliveira ([arXiv:1112.3914](https://arxiv.org/abs/1112.3914) v1, Prop. 16, which gives no lower bound) have always paid. The term does not follow from any checked theorem. Because the hard oracle ignores the query, the bound is really an estimation lower bound: it holds even if the algorithm observed `Z_t` directly.

**Search coverage.** Searched 2026-11-18 (UTC) across arXiv and the web for lower bounds under polynomial or β-mixing, high-probability minimax bounds and Markovian SGD. Sarkar et al. was read in part; its Thm 4 wording comes from a partial HTML read. Not rechecked: Nagaraj et al. (NeurIPS 2020, geometric mixing, expected error), and classical dependent-process work (Rio, Bradley, Doukhan) on the optimality of moment and Fuk–Nagaev deviation inequalities under polynomial mixing. That classical work concerns the sample mean, not every estimator, but it could contain an equivalent `δ^(−1/β)` obstruction. The companion note's citations are consistent with what I read. One correction: in Sarkar et al. the lower bounds are Thm 2 / Cor. 2 / Thm 4; Corollary 3 is an upper bound.

**Conclusion**

**Yes, the necessary budget is larger than any lower bound I checked, mainly through a new confidence term `τδ^(−1/β)`.** The strongest relevant baseline is the repository's own earlier polynomial-mixing lower bound. That bound already gives the accuracy exponent `(GR/ε)^(a(1+1/β))`, but only for expected gap. Sarkar et al. study geometric mixing and give constant-confidence bounds with no `δ`.

| | Necessary calls (fixed `p, β`) |
|---|---|
| Earlier bound | `τ·(GR/ε)^(a(1+1/β))` (expected gap; different class) |
| This result | `τ·[(GR/ε)^(a(1+1/β))·log(1/δ) + δ^(−1/β)]` (probability `1−δ`) |

The gain is polynomial when `1/δ ≳ (GR/ε)^(a(β+1))`. In that regime, no method can have logarithmic confidence dependence under polynomial mixing. Together with the companion upper bound, this settles the polynomial exponents of `ε`, `δ` and `τ` up to `log(1/δ)` powers. The constants degrade exponentially in `a(1+1/β)`.

The construction is elementary: linear objectives, an oracle that ignores the query, and one rare stretch with no information. The accuracy part is a routine high-probability version of the earlier argument. Priority is supported only by my search. I did not check classical deviation-optimality results for polynomially mixing sums, and they could contain an equivalent obstruction.

What can be claimed: a new, near-matching lower bound showing that, in this oracle model, polynomial mixing forces a polynomial `τδ^(−1/β)` confidence cost.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
