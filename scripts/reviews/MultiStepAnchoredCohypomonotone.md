# Multi-step anchored forward–backward for cohypomonotone inclusions: novelty assessment

The [theorem](../../LongTails/Theorems/MultiStepAnchoredCohypomonotone.lean) proves that, for every instance of the [setup](../../LongTails/Setups/CohypomonotoneInclusion.lean), the deterministic [anchored method with a fixed-length inner forward–backward loop](../../LongTails/Algorithms/MultiStepAnchoredForwardBackward.lean) returns its final iterate u together with ξ ∈ H(u) and ‖F(u)+ξ‖ ≤ ε. The setup is any real inner-product space, with F L-Lipschitz, H monotone with exact resolvents J_γ for all γ>0, F+H two-point ρ-cohypomonotone, 0 ≤ ρ, ρL < 1, and a zero x* with ‖x₀−x*‖ ≤ R.

**Complexity.** Here L is the Lipschitz constant of F, ρ is the cohypomonotonicity modulus, δ = 1−ρL ∈ (0,1], R bounds the initial distance, and ε is the residual target. Each F evaluation and each resolvent costs one call. The proved budget is 2+(2m+3)n with m = ⌈2δ⁻¹ln(16/δ)⌉ and n = ⌈16LR/(δε)⌉, so

  **O( 1 + (LR/((1−ρL)²ε) + [R>0]/(1−ρL)) · log(e/(1−ρL)) ).**

The updates use L, ρ and x₀; R and ε enter only the stopping budget. There is no log(1/ε), but each outer step costs Θ(δ⁻¹log(e/δ)) calls, so the method is double-loop.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Alacaoglu–Kim–Wright, [arXiv:2402.05071](https://arxiv.org/abs/2402.05071) (ICML 2024; v3 26 Sep 2026), Thm 2.1, Cor 2.2, Rem 2.3. Direct competitor on the same class. I take η=(1+ρL)/(2L), which is admissible since ρ<η<1/L; then η−ρ=δ/(2L) and 1−ηL=δ/2. | K=⌈8LR/(δε)⌉ outer steps with N_k=⌈4(1+ηL)/(1−ηL)·log(98√(k+2)log(k+2))⌉ inner FBF steps, giving O(1/δ + (LR/(δ²ε))·log(e+LR/(δε))) → O(1 + (LR/(δ²ε)+1/δ)·log(e/δ)) | The accuracy logarithm log(e+LR/(δε)) is replaced by log(e/δ). The speedup is Θ(1+log(e+LR/ε)/log(e/δ)), which is large for fixed ρL and ε→0. The new result is worse by up to a log(e/δ) factor when LR ≲ ε, because its inner loop is longer in the early iterations. | Their assumptions are ℝᵈ and maximal cohypomonotonicity of F+H. Here the space is any inner-product space and maximality of the sum is not assumed. I found no natural instance gained: in Hilbert space, surjectivity of I+η(F+H) (from the forward–backward contraction) should already imply maximality by a Minty-type argument, though I did not check this in detail. | None. Both use known L and ρ and give a last-iterate guarantee on dist(0,F+H). Remark 2.3 converts their fixed-point residual without changing the order (via Cai et al., Lemma C.4); I did not re-derive that step. | None beyond the constants. Both methods are double-loop. |
| Cai–Oikonomou–Zheng, composite FEG, [arXiv:2206.05248](https://arxiv.org/abs/2206.05248) v6 (ICML 2024), Thm 4.1. Special-case baseline: only ρL<1/2. | With η=1/L, the residual is ≤2LR/((1−2ρL)T) at O(1) calls per step, so O(1+LR/((1−2ρL)ε)) → O(1+(LR/(δ²ε)+1/δ)·log(e/δ)) | On the overlap ρL<1/2 we have δ>1/2. The new result wins only when 1−2ρL is below a small universal constant, i.e. ρL very close to 1/2. Elsewhere it is worse by a constant factor. | Range ρL<1/2 → ρL<1. The classes are nested, and 1/2 ≤ ρL < 1 becomes covered without a log(1/ε) factor. | None. Both are last-iterate residual guarantees with known parameters. | The new method needs an inner loop of length Θ(δ⁻¹log(e/δ)), whereas COZ is single-loop. |

Other rows were checked and excluded. Tran-Dinh ([2302.04099](https://arxiv.org/abs/2302.04099)) and Lee–Kim FEG apply only for 2ρL<1, which is dominated by row 2. Pethick et al. (ICLR 2025) give an O(ε⁻²) best-iterate rate, as reported by AKW and the companion note; I did not verify it.

**Reduction check and proof ancestry.** I found the result follows by a standard reduction from a source nine days older than it:

1. **Change of variables.** For g ∈ (F+H)(u), set w = u+ρg. Cohypomonotonicity makes the graph (w,g) monotone; this is the Bauschke–Moursi–Wang transformation that AKW also use. Because η−ρ = s, the selected update rewrites exactly as w_{k+1} = β_k y₁ + (1−β_k)w_k − s·g_{k+1} + e_k.
2. **Match to Jiang–Yoon.** This is the anchored extra-proximal (AEP) step of [Jiang–Yoon, arXiv:2609.30212](https://arxiv.org/abs/2609.30212) v1 (24 Sep 2026, unreviewed, monotone inclusions only), Theorem 3.2. The anchor is y₁, the step is s, and the error is r = e_k.
3. **Their error condition.** Their relative-error condition ‖r‖ ≤ ‖z_{k+1}−z_{k+1/2}‖ = ‖e_k − s·w_k‖ follows from ‖e_k‖ ≤ (s/2)‖w_k‖. The selected proof gets that bound from a warm-started q-contraction, with q = 1−δ/2, in m steps; see `parameter_bounds`.
4. **Why the proof transfers.** Their Appendix A.2 uses monotonicity only between iterates and the solution, so the proof carries over even though the transformed graph is not literally "F+H with H maximal".
5. **Resulting rate.** This yields ‖g_n‖ ≲ ‖y₁−x*‖/(ns) ≤ 4R/(ns), which is the selected rate.

The mechanism is therefore inherited: making the inner error proportional to the anchored difference is the AEP principle. What remains new is noticing that the reduction applies, plus the routine inner-contraction certificate.

**Search coverage (2026-10-07 UTC).**

- **Sources read:** current arXiv text of AKW v3 (Thm 2.1, Algorithm 1, §5 open problem (ii) "first-order complexities without spurious log terms and extended range for ρ"), Jiang–Yoon v1 (Thm 3.2, App. A.2, §7), and COZ v6 (Thm 4.1 and the footnote stating the open problem).
- **Searches:** arXiv and the ICML/ICLR proceedings for log-free full-range results.
- **Not verified theorem by theorem:** Pethick et al., and [arXiv:2605.30905](https://arxiv.org/abs/2605.30905), whose abstract does not mention cohypomonotonicity.
- **Chronology:** Git introduces the result in `7f267d8` on 2026-10-03. Jiang–Yoon is therefore prior, not "concurrent" as the companion note says. The note does concede the derivation from Jiang–Yoon, and its log-free claim relative to AKW is accurate. No subsequent superseding result was found.
- **Repository overlap:** [AnchoredGeneralizedMonotone](../../LongTails/Theorems/AnchoredGeneralizedMonotone.lean) overlaps only on monotone root finding.

## Conclusion

**Yes, the log(1/ε) factor is removed on the full range ρL<1, but the result is a short corollary of a slightly earlier framework.**

The strongest baseline on the identical class is Alacaoglu–Kim–Wright's inexact Halpern method. With δ = 1−ρL:

| | total calls |
|---|---|
| AKW (2024) | O(1/δ + (LR/(δ²ε))·log(e + LR/(δε))) |
| this result | O(1 + (LR/(δ²ε) + 1/δ)·log(e/δ)) |

The gain is a factor of about log(LR/ε)/log(e/δ), which is substantial when LR/ε ≫ 1/δ. When LR ≲ ε, the new result loses up to a factor of log(e/δ). On ρL<1/2, composite FEG remains single-loop and better except very near ρL=1/2.

This complexity comparison establishes a real gain, and it answers the log-free half of AKW's stated open problem. Priority is weaker. Jiang–Yoon's AEP Theorem 3.2, posted nine days before this result, yields it through the standard change of variables w = u+ρg plus a routine contraction bound for the inner loop. The single-loop question also remains open.

The claimable contribution is an explicit, verified, log-free accelerated bound for cohypomonotone inclusions on the full range ρL<1. It is obtained by applying the AEP relative-error mechanism, not by a new technique.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
