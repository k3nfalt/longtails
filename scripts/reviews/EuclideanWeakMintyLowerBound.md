# Novelty assessment: EuclideanWeakMintyLowerBound

The [theorem](../../LongTails/Theorems/EuclideanWeakMintyLowerBound.lean) proves the following on the [setup](../../LongTails/Setups/EuclideanWeakMinty.lean), which places no algorithm restriction. Take any valid parameters, any randomized algorithm and any call count N ≤ budget, including N = 0. Then some L-Lipschitz operator on ℝᵈ that has a zero x* with ‖x* − x₀‖ ≤ R and satisfies the weak-Minty inequality (here already with ρ = 0) makes the algorithm fail, meaning E‖F(x̂)‖ > ε or the residual is not integrable. The hard instance is built in [MintyChainGeometry](../../LongTails/Proofs/MintyChainGeometry.lean) and [MintyChainLowerBound](../../LongTails/Proofs/MintyChainLowerBound.lean).

**Proved necessary calls.** Here L is the Lipschitz constant, R bounds the distance from x₀ to the solution, ε is the expected-residual target and d is the dimension. The domain is 28ε ≤ LR, d ≥ 257 and 0 ≤ ρ ≤ 1/(20L). The exact budget is ⌊min{(LR/(28ε))², (d/257)^{1/3}}⌋ − 1, which gives

  N ≥ Ω( min{ L²R²/ε², d^{1/3} } ).

The bound is vacuous when LR/ε is only slightly above 28.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Yoon–Ryu, ICML 2021](https://proceedings.mlr.press/v139/yoon21d.html), Thm. 3, monotone special case (monotone with a zero ⇒ Minty with ρ = 0) | Ω(LR/ε) → Ω(min{L²R²/ε², d^{1/3}}) | The necessary budget grows from LR/ε to (LR/ε)² when d ≥ 257(LR/(28ε))⁶. More generally it is larger whenever d^{1/3} ≫ LR/ε. | Monotone hard instance → non-monotone (and non-comonotone) Minty instance | Deterministic span-restricted methods, last iterate → arbitrary randomized methods and any output, expected residual | Needs d polynomial in LR/ε, roughly d ≳ (LR/ε)³ to beat the old bound. Yoon–Ryu needs only d of order N. |
| [Diakonikolas–Daskalakis–Jordan, AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), Thm. 3.2 (EG+ upper bound, ρ < 1/(8L)); repository [upper theorem](../../LongTails/Theorems/EuclideanWeakMintyExtragradient.lean), budget 2 + 2⌈200L²R²/ε²⌉ | Upper O(L²R²/ε²) vs lower ⌊(LR/(28ε))²⌋ − 1 | Not an improvement over an upper bound. It certifies that the upper bound is optimal up to a factor of about 3·10⁵ (400·784; the companion note says 1.3·10⁵) when d ≥ 257(LR/(28ε))⁶. | None | None | For d^{1/3} < (LR/ε)², a gap remains between the lower bound d^{1/3} and the upper bound (LR/ε)². |

**Reduction check.** Known Ω(ε⁻²) stationarity lower bounds do not transfer. The bounds of [Carmon et al.](https://arxiv.org/abs/1710.11606) are for nonconvex gradients. A gradient field that satisfies Minty comes from a star-convex f, and for those f, ‖∇f‖² ≤ 2L(f − f*), so star-convex acceleration reaches ‖∇f‖ ≤ ε in Õ(LR/ε) calls. Affine Minty operators are monotone. The hard instance therefore has to be a nonlinear, non-gradient operator. The mechanism (a gated chain in which each link has length ε/L, hidden in random coordinates) appears to be new for this class. As proof ancestry, it reuses the repository's prefix-simulation counting lemma, which supplies the randomized hiding argument, and the Nemirovski / Carmon-style chain idea. The specific Minty-compatible gating is the part I could not find in prior work.

**Search coverage.** I searched on 2026-11-17 for "weak Minty", "Minty", "star-monotone", "pseudo-monotone" and "nonmonotone VI" combined with "lower bound" / "acceleration". I checked DDJ 2021, Böhm ([arXiv:2201.12247](https://arxiv.org/abs/2201.12247), TMLR 2023, whose open-question passage exists, though I did not read its full context), Lin–Jordan ([arXiv:2205.03202](https://arxiv.org/abs/2205.03202)), Anagnostides et al. ([arXiv:2504.03432](https://arxiv.org/abs/2504.03432)), [arXiv:2405.15990](https://arxiv.org/abs/2405.15990) and recent monotone randomized lower bounds ([arXiv:2611.20296](https://arxiv.org/abs/2611.20296), [arXiv:2609.13462](https://arxiv.org/abs/2609.13462)). None contains an Ω(ε⁻²) residual lower bound for Minty operators. I did not reread every theorem in the full text. Git history shows the result was added on 2026-11-17 (commit 98684e93). I did not check the companion note's claim that cutting-plane methods need O(d log(LR/ε)) calls in fixed dimension. The note's "Θ(L²R²/ε²) in high dimension" is accurate only under d ≥ 257(LR/(28ε))⁶.

## Conclusion

**Yes: this is a new, essentially tight lower bound showing that Lipschitz Minty/weak-Minty problems cannot be accelerated in high dimension.**

The strongest previous applicable lower bound came from the monotone special case (Yoon–Ryu), and it covered only deterministic span methods. The strongest upper bound is DDJ's EG+:

| | Necessary / sufficient calls for E‖F(x̂)‖ ≤ ε |
|---|---|
| Previous lower (monotone, span methods) | Ω(LR/ε) |
| This result (any randomized method) | Ω(min{L²R²/ε², d^{1/3}}) |
| Upper (DDJ EG+; repository EG) | O(L²R²/ε²) |

When d ≥ 257(LR/(28ε))⁶, the upper and lower bounds match up to a universal constant with no logarithm, and this settles the acceleration question Böhm posed. The proof is not a reduction from nonconvex or monotone lower bounds: those either do not satisfy Minty or admit Õ(LR/ε) methods.

What remains limited is the dimension requirement. For (LR/ε)³ ≲ d ≲ (LR/ε)⁶ the bound is only d^{1/3}, and below that it says nothing beyond the old Ω(LR/ε). My search found no prior Ω(ε⁻²) bound, but absence from a search does not prove priority. What can be claimed is the first verified randomized lower bound Ω((LR/ε)²) for the Lipschitz Minty class in sufficiently high dimension, which matches extragradient.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
