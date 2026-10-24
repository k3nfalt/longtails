# Novelty assessment: RelativeErrorGeneralizedAcceleration

The [theorem](../../LongTails/Theorems/RelativeErrorGeneralizedAcceleration.lean) considers a convex objective on a real Hilbert space that is generalized-smooth in segment form, ‖∇f(x)−∇f(y)‖ ≤ (L₀+L₁M)‖x−y‖ whenever ‖∇f‖ ≤ M on the segment. A minimizer must exist with ‖x₀−x*‖ ≤ R and f(x₀)−f* ≤ Δ. Every gradient reply v may be adversarial and history-dependent but satisfies ‖v−∇f(x)‖ ≤ α‖∇f(x)‖ with 0 ≤ α ≤ 1/100 ([setup](../../LongTails/Setups/RelativeGeneralizedSmoothConvex.lean)). Under these conditions, the last iterate of a projected accelerated method ([algorithm](../../LongTails/Algorithms/RelativeGeneralizedAcceleration.lean)) satisfies f(x_N)−f* ≤ ε on every oracle path. The method uses L₀, L₁, R, Δ, α, ε and the horizon N.

**Complexity.** The proved budget is `⌈2⁶⁰[…]⌉` gradient replies, with one reply per step and no function values or line search. Up to constants it is

N = O( √(L₀R²/ε) + α²L₀R²/ε + (1+L₁R)·ℓ + α²L₁²R²·ℓ² ),  where ℓ = 1 + log(2 + L₀R²/ε + L₁R + Δ/(L₀R²)).

Here ε is the target accuracy, α is the relative-error level, and L₀, L₁ are the smoothness constants.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884) (v2, 21 May 2026; the note says ICML 2026, which I did not verify), Thm 4.3. **Exact gradients only (α=0)** | O(√(L₀R²/ε) + L₁R·log₊min{L₁²Δ/L₀, Δ/ε} + log₊(Δ/(L₀R²))) → at α=0: O(√(L₀R²/ε) + (1+L₁R)ℓ) | None: same leading term. The new bound is slightly worse in the logarithmic argument; for example, it is L₁R·log(L₀R²/ε) where Tyurin has L₁R·log(L₁²Δ/L₀) | Exact gradient → adversarial relative error α ≤ 1/100 | None (both give a last-iterate bound with known Δ and R) | Restricted to α ≤ 1/100; needs a projection ball |
| Repository [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean). **Exact gradients, Hessian-form class** | O(1 + √(L₀R²/ε) + (L₁R)^{2/3}·log(4+4Δ/ε)) → O(√(L₀R²/ε) + (1+L₁R)ℓ) | Worse at α=0: (L₁R)^{2/3} → L₁R | Exact → relative-error oracle | None | Worse transient in L₁R |
| Repository [AcceleratedRelativeErrorConvex](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean); Vasin–Tyurin–Gasnikov, [arXiv:2610.24863v1](https://arxiv.org/abs/2610.24863) (17 Oct 2026), Thm 3.3 and Remark 3.1. **Global L-smoothness (L₁=0) only** | O(√(LR²/((1−α)ε)) + α²LR²/((1−α)ε)) → at L₁=0: O(√(L₀R²/ε) + α²L₀R²/ε + ℓ) | None: same order, plus an additive log | L-smooth → (L₀,L₁)-smooth, so curvature may be unbounded (e.g. cosh) | None | α ≤ 1/100 instead of α < 1 |
| Kovalev–Stonyakin, [arXiv:2607.26969v2](https://arxiv.org/abs/2607.26969) (4 Aug 2026), Thm 3.1. **Normalized-direction oracle** | Nonaccelerated O(max{L₁², L₀/ε}) for the best iterate, and only when the direction tolerance shrinks with ε → not applicable at fixed α | Not comparable: with α fixed and independent of ε their theorem does not apply | Incomparable: their oracle supplies no gradient magnitude | Theirs: best iterate; this result: last iterate | This result needs gradient magnitudes and Δ |

**Reduction check.** Plugging into a global-smoothness relative-error theorem fails. For f(x)=cosh(x) (L₀=L₁=1), the curvature on a ball of radius 2R is about e^{2R}, so freezing curvature gives exponentially large terms in L₁R; the competing methods also do not stay in the ball. A sublevel-set reduction with L ≈ L₀+L₁²Δ would need a monotone accelerated method, and the oracle gives no function values. Even if that reduction worked, it would cost an extra L₁R√(Δ/ε). Ancestry: the α²-weighted horizon budget follows the repository's L-smooth relative-error analysis, and the √T + L₁R-type transient follows Tyurin's line of work. The new step is a ball projection combined with a normal-cone bound. This controls the true gradient under transverse errors and lets the generalized-smooth curvature bound and the error-tolerant potential hold simultaneously.

**Search coverage.** On 2026-10-24 (UTC) I searched arXiv and the web for relative or inexact gradients combined with (L₀,L₁) or generalized smoothness, read the theorem statements of the four sources above, and checked ARC-SG ([arXiv:2609.06555](https://arxiv.org/abs/2609.06555)), which assumes unbiased sub-Gaussian noise and so does not apply. I did not verify the note's PMLR link or its "Descending Everest" citation (arXiv:2610.21461); the theorems of Vasin et al. [arXiv:2102.02921](https://arxiv.org/abs/2102.02921) are also unread. The result was committed on 2026-10-24 (commit 1e159fe), one week after Vasin–Tyurin–Gasnikov v1. I found no discrepancy between the note and the Lean statement.

## Conclusion

**The rate is not new in either special case; what is new is an end-to-end guarantee in a setting no checked prior theorem covers.**

The strongest baselines are Tyurin's Theorem 4.3 for exact gradients and the accelerated relative-error bound for globally smooth f. When L₁ = 0 this result matches the second, and when α = 0 it matches the first in order. It is worse than the repository's exact-gradient (L₁R)^{2/3} transient.

| Setting | Best checked prior | This result |
|---|---|---|
| α>0, L₁>0 | none (global-smoothness reductions are exponential in L₁R) | √(L₀R²/ε) + α²L₀R²/ε + (1+L₁R)ℓ + α²L₁²R²ℓ² |

This removes the global-smoothness restriction from accelerated relative-error optimization at polynomial cost in L₁R. The new instances are convex objectives with unbounded curvature, such as cosh-type functions, accessed through biased gradients with a certified relative error. The price is the fixed cap α ≤ 1/100 and a slightly weaker transient. Optimality for this oracle class is not established.

The comparisons support this scope gain. Priority rests on a targeted search over recent preprints; an unindexed concurrent result could change that. The claimable contribution is the first verified accelerated last-iterate guarantee, polynomial in L₁R, for convex generalized-smooth optimization with adversarial relative gradient errors.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
