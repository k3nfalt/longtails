# Novelty assessment: accelerated composite optimization under feasible-domain Hessian–gap bounds

[`FeasibleGapAccelerated.result`](../../LongTails/Theorems/FeasibleGapAccelerated.lean) ([setup](../../LongTails/Setups/FeasibleHessianGapComposite.lean), [algorithm](../../LongTails/Algorithms/FeasibleGapAccelerated.lean)) proves the following. Let F = f + ψ with f, ψ convex on a convex set Q in a Hilbert space, exact Q-constrained regularizer prox, and a minimizer x⋆ ∈ Q. At every x ∈ Q, assume ∇f has a Fréchet derivative H(x) ⪰ 0 with ‖H(x)‖ ≤ H₀ + H₁(F(x) − F⋆). Then restarted accelerated dual averaging deterministically returns a feasible final iterate x̂ with F(x̂) − F⋆ ≤ ε.

**Proved budget.** R ≥ ‖x₀ − x⋆‖, Δ ≥ F(x₀) − F⋆, H₀, H₁ ≥ 0, ε, R, Δ > 0. All five quantities are known to the method. The number of gradient plus prox calls is

  O( (1 + R√(H₀/ε + H₁)) · log²(4 + R²(H₀/ε + H₁)) · log(2 + Δ/ε) ).

This is the Lean budget with the constant 2²⁴ suppressed. There is no dimension factor, and function values are never queried.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/abs/2609.33415) (27 Sep 2026, preprint, prior), Thm 9 at σ = 0. **Only unconstrained f, ψ ≡ 0**: its projection set Q is auxiliary and "does not constrain" the problem (§3–4.1). | Õ(log(Δ/ε) + R√(H₀/ε) + R√H₁·min{log(Δ/ε), log(H₁Δ/H₀)}) → the bound above | Worse on the overlap: extra log²(R²(H₀/ε+H₁)) on both terms, and log(Δ/ε) on the H₀ term | Unconstrained f with ∇f(x⋆) = 0 → constrained composite f + ψ on Q, with curvature needed only at feasible points | None | Requires a Hessian at feasible points, not their first-order local model. Exact oracles only; Thm 9 also handles heavy-tailed noise |
| Lu–Mei, [arXiv:2206.01209v3](https://arxiv.org/abs/2206.01209) (SIOPT), Thm 2 (APG with backtracking) on composite f + P | O(√((Δ + R²/γ₀)·max(1, γ₀L_Ŝ)/ε)) iterations, each with up to O(log(γ₀L_Ŝ)) backtracking steps using F-values. Here L_Ŝ is the Lipschitz constant of ∇f on an enlarged ball of radius ≥ R around x⋆ in dom P. L_Ŝ cannot be bounded by H₀, H₁, R, Δ → the bound above | On the example below, L_Ŝ ≥ e^R gives Ω(R e^{R/2}/√ε) → Õ(R/√ε): an exponential-in-R gain against that proved upper bound | Ball-local Lipschitz ∇f, with f finite on ℝⁿ satisfying the tangent inequality (3) at all y ∈ ℝⁿ → feasible-point Hessian–gap bound with no ambient convexity | None (both are last-iterate) | Needs known H₀, H₁, R, Δ; Lu–Mei needs none of these, but uses function values |
| Repository [CompositeGapAccelerated](../../LongTails/Theorems/CompositeGapAccelerated.lean) (commit 0dc2692, 2026-10-26; not literature): globally convex f with an ambient quadratic model | O((1+R√(H₀/ε+H₁))·log(4+R²(H₀/ε+H₁))·log(2+Δ/ε)) → the bound above | Worse by one factor of log(4+R²(H₀/ε+H₁)) where both apply | Ambient convex model → feasible-only Hessian bound. The classes are **incomparable**: the new class drops global convexity and ambient bounds but adds twice-differentiability | None | Extra logarithm; Hessian formulation |

**Reductions and mechanism.** Global smoothness gives no reduction: on Q ∩ {F − F⋆ ≤ Δ}, curvature is ≤ H₀ + H₁Δ. However, accelerated query points are not known to stay in that sublevel set, and even if they did, the result would be R√((H₀+H₁Δ)/ε), polynomially worse when H₁Δ ≫ H₀. The obstacle to transferring Lobanov et al. is their Lemma 4 self-bound ‖∇f‖² ≤ 2C⋆F·(H₀+H₁F), which needs ∇f(x⋆) = 0 and ambient descent points. Here that bound is replaced by a dyadic feasible-segment bound on the shifted term h. The cumulative-prox control of j and the restart scheme are inherited from the sibling proof. Proof ancestry: Xiao-type accelerated dual-averaging energy algebra and the phase restarts of Lobanov et al. I did not audit the Lean proofs or run the build or comparator.

**Example check.** Let Q = {t ≥ 1}, f = ‖Au‖²/t + e^{aᵀu}, and ψ = t − aᵀu, with ‖A‖ = ‖a‖ = 1. Then x⋆ = (0,1) and the gap is ‖Au‖²/t + (e^q − q − 1) + (t − 1), where q = aᵀu. Using ‖∇²(‖Au‖²/t)‖ ≤ 2‖A‖² + 2‖Au‖²/t and e^q ≤ 2(e^q − q − 1) + 2 gives H₀ = H₁ = 4. With x₀ = (−Ra, 1), we have Δ ≤ R² + R, while (Ra, 1) in the R-ball has curvature e^R. Tangent planes at (−ra, 2), evaluated at (0, −1), diverge, so no finite f on ℝⁿ satisfies Lu–Mei's (3). Caveat: the regrouping f̃ = e^{aᵀu}, ψ̃ = ‖Au‖²/t + t − aᵀu + ι_Q places the example in the ambient sibling class, but it requires a perspective-prox oracle.

**Search coverage.** On 2026-10-29 UTC I read the theorem and setting sections of 2609.33415v1, 2608.04884v1 (unconstrained; needs f⋆, F-values, and line search), and 2610.33761v1 (Yu–Lin: unconstrained NAG, non-restarted). I also read Lu–Mei §2 (Lemma 1, Thms 1–2). Searches for constrained or composite gap-curvature acceleration found nothing; Tyurin's 2508.06884 (ICML 2026) concerns unconstrained ℓ(‖∇f‖)-smoothness and was not read in full. I did not read the hidden logarithms of 2609.33415 or the full 2026 ICML/ICLR/NeurIPS proceedings. The result was introduced in commit 7755564 on 2026-10-29, after all cited preprints. The companion note's characterization of these sources matches what I read. Its Hessian constants (H₀ = 4‖A‖² + 2‖a‖², H₁ = 4 + 2‖a‖²) are valid but looser than mine.

## Conclusion

**The rate is not better; the gain is scope: gap-curvature acceleration now works for constrained composite problems whose smooth part is controlled only on the feasible set.**

The strongest gap-curvature baseline, Lobanov–Dvinskikh–Gasnikov Thm 9, covers only unconstrained problems. On that overlap it is faster by logarithms:

| | calls |
|---|---|
| 2609.33415 (Q = E, ψ = 0) | Õ(R√(H₀/ε) + R√H₁ log(Δ/ε)) |
| this result | O((1 + R√(H₀/ε+H₁)) log²(R²(H₀/ε+H₁)) log(Δ/ε)) |

The repository sibling already extended this rate to composite problems, with one fewer logarithm, but it needs a globally convex f with an ambient quadratic model. The new class instead needs only feasible-point Hessian bounds. The checked perspective-plus-exponential example satisfies every hypothesis, yet admits no finite convex extension and has local curvature e^R. The general-purpose local-smoothness APG of Lu–Mei therefore gives only exponentially worse bounds in R, while this result stays polynomial up to logarithms.

The comparison establishes this scope gain over the checked baselines, at the price of one extra logarithm and a twice-differentiability assumption. Priority looks plausible, since I found no constrained gap-curvature acceleration, but this subfield is moving quickly. The example is also reachable by the sibling theorem under a different split that requires a perspective-function prox oracle. The claimable contribution is an accelerated, value-free guarantee under gap-dependent curvature for constrained composite problems, requiring curvature control only on Q. This is an incremental extension of the sibling result's scope, not a rate improvement.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
