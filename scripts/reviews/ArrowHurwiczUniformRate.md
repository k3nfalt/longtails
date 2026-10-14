# Arrow–Hurwicz with a constant step: uniform O(1/T) ergodic gap on bounded composite saddle problems

[`result`](../../LongTails/Theorems/ArrowHurwiczUniformRate.lean) proves the following. Run the Arrow–Hurwicz method ([algorithm](../../LongTails/Algorithms/ArrowHurwicz.lean); this is PDHG with θ = 0, or projected alternating GDA when g = h = 0) with step η = 1/(2L) for T = ⌈200R(LR+M)/ε⌉ iterations. Then the uniform averages (x̄_T, ȳ_T) lie in X × Y and satisfy sup_{x∈X, y∈Y} Φ(x̄_T, y) − Φ(x, ȳ_T) ≤ ε. Here Φ(x,y) = g(x) + ⟨y,Kx⟩ − h(y) ([setup](../../LongTails/Setups/BoundedCompositeSaddle.lean)). The guarantee is deterministic.

**Complexity.** The setup has convex sets X, Y in arbitrary real inner-product spaces with ‖x‖, ‖y‖ ≤ R, a linear map with ‖K‖ ≤ L, and convex g, h that are M-Lipschitz on X, Y. The oracle answers K, K*, and the exact prox maps of g+ι_X and h+ι_Y, at 4 calls per iteration. The proved budget is 4⌈200R(LR+M)/ε⌉, so

  **N = O(1 + LR²/ε + MR/ε)** oracle calls.

The supporting lemma `Hyp.uniform_total` gives the gap bound (81R²/η + 28MR)/T for every η ≤ 1/(2L).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| PDHG (θ = 1), Chambolle–Pock, JMIV 2011, [Thm 1(b)](https://optimization-online.org/2010/06/2646/) (prior) | τ = σ = 1/(√2L), so τσL² = ½ < 1. The gap is ≤ D/N with D ≤ 2R²(1/τ + 1/σ) = 4√2·LR², at 4 calls/iteration with the same oracle: O(1 + LR²/ε) → O(1 + LR²/ε + MR/ε) | **Worse** by a factor 1 + M/(LR) when M > LR; **none** (same order) when M ≤ LR | None. CP state the result in finite dimensions, but its telescoping proof is algebraic and carries over to this setting. | None. Both use ergodic averages and the same full gap, and both need L. | AH carries an extra MR/ε term. The only difference is the algorithm (θ = 0 instead of θ = 1). |
| AltGDA, Nan–Iyengar–Kroer–Das Gupta, [arXiv:2609.32995v1](https://arxiv.org/abs/2609.32995) Thm 1 (26 Sep 2026, preprint; prior) — **special case: simplices, g = h = 0** | η = δ/(2√2L), so the gap is ≤ 15√2·L/(δT): O(1 + L/(δε)) → O(1 + L/ε) (here R = 1, M = 0) | Removes the 1/δ factor for this algorithm. δ ≤ min of the equilibrium's support probabilities, so δ → 0 is possible. The constant-level gain needs δ < 15√2/162 ≈ 0.13. | Simplices only → any bounded convex sets, and composite Lipschitz g, h | Step depends on δ, which is generally unknown → step 1/(2L), which needs only L | Constant 162 vs 15/2 when δ is large. Their Thm 2 (general compact sets) is conditional on LMI feasibility. |
| Same setup in this repo, [`ArrowHurwiczBoundedSaddle`](../../LongTails/Theorems/ArrowHurwiczBoundedSaddle.lean) (d7fe8d4, 5 Oct 2026) | O(1 + (R(LR+M)/ε)^{4/3}) → O(1 + R(LR+M)/ε) | ε^{-4/3} → ε^{-1}, for this method only | None | T-dependent step → constant step | None |

**Reduction check.** I found no substitution or change of variables that turns the θ = 0 iteration with projections into PDHG or mirror-prox. The bound on total friction is a new argument: an all-lag, non-causal, band-vanishing multiplier built from cyclic monotonicity of prox. The one-step Lyapunov and finite-history LMI arguments in the literature do not give it. Proof ancestry: the gap-to-friction reduction (`Hyp.one_step_sum`) follows the standard Chambolle–Pock and Arrow–Hurwicz telescoping. Zames–Falb/IQC multipliers (Lessard–Recht–Packard 2016) supply the idea of weighting monotonicity inequalities. Neither framework gives the O(1/T) bound by itself.

**Search coverage (2026-10-07).** I checked the following directly:
- Chambolle–Pock 2011, Thm 1 and §3.2. With bounded dom F* they state only O(1/√N) for θ = 0.
- Nan et al., arXiv:2609.32995v1, Thm 1 and Thm 2.
- Nan et al., ICLR 2026 ([arXiv:2510.03855](https://arxiv.org/abs/2510.03855)), via its abstract.

Alternating mirror descent ([Wibisono–Tao–Piliouras 2022](https://arxiv.org/abs/2206.04160), O(K^{-2/3}); [Katona–Wang–Wibisono, JMLR 2026](https://jmlr.org/papers/v27/24-0792.html), O(K^{-4/5})) was checked only at the abstract level. I did not search He–You–Yuan-type θ = 0 analyses or other non-English sources in depth.

The companion note's citations match these sources. However, the note never compares against PDHG or mirror-prox on the same problem class, and that comparison is decisive. Its "matches lower bounds" remark describes the 1/T order only, not an optimal constant or M-dependence.

## Conclusion

**No optimization advantage: the result is a new analysis of one specific method, and applicable methods already match or beat its complexity.**

The strongest baseline is Chambolle–Pock PDHG (θ = 1). It uses the same four oracle calls per iteration, the same averaged output, and the same knowledge of L. On exactly this problem class it gives

  PDHG: O(1 + LR²/ε)  vs.  this result: O(1 + LR²/ε + MR/ε).

So the two bounds have the same order when M ≤ LR, and the new bound is worse by a factor 1 + M/(LR) otherwise.

What is new is about the Arrow–Hurwicz method itself. Previously, the best unconditional fixed-step O(1/T) bound for this method that I found was Nan et al.'s, and it holds only on simplices with a step proportional to an equilibrium-dependent constant δ. This result removes δ, whose 1/δ factor can be arbitrarily large, and it covers general bounded convex sets and Lipschitz composite terms. The friction-multiplier proof appears to be a new mechanism. Priority rests on a search completed on 2026-10-07, and the only close preprint is dated 26 Sep 2026.

The claimable contribution is the first unconditional, uniform O(1/T) ergodic guarantee for constant-step Arrow–Hurwicz (alternating projected GDA). It does not improve the complexity of solving bounded composite saddle problems.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
