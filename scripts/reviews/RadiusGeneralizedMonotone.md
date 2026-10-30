# Radius-only residual complexity for monotone (L0, L1)-Lipschitz root finding

The [theorem](../../LongTails/Theorems/RadiusGeneralizedMonotone.lean) covers continuous monotone F on a real inner-product space that satisfy the segment condition ‖F x − F y‖ ≤ (L0 + L1·max_seg‖F‖)‖x − y‖ and have a root x* with ‖x0 − x*‖ ≤ R ([setup](../../LongTails/Setups/RadiusGeneralizedLipschitzMonotone.lean)). For every such F, the [warm-started anchored algorithm](../../LongTails/Algorithms/WarmAnchoredMonotone.lean) returns a last iterate with ‖F(x)‖ ≤ ε deterministically after 2⌈2¹⁵(1 + L0R/ε + (L1R)^{4/3})⌉ exact F-evaluations. Here L0 > 0 and L1 ≥ 0 are the Lipschitz constants, R is the initial distance to a root and ε is the target residual. No bound on ‖F(x0)‖ is assumed. The updates use L0, L1, R and x0.

**Complexity:** N = O(1 + L0R/ε + (L1R)^{4/3}).

The C·log(1+A) term hidden in the anchored finish is absorbed, as the Lean budget certifies. At L1 = 0 the bound is O(1 + L0R/ε), and at R = 0 it is O(1).

Below, A = L0R/ε and C = L1R are shorthand for the table only.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Choudhury–Loizou, EG with step ν/(L0+L1‖F x_k‖), [arXiv:2510.22421v1](https://arxiv.org/abs/2510.22421) Thm 3.6 (NeurIPS 2025). Prior. | Need K+1 ≥ 2(L1R)²/ν² + 2(L0R/ε)²/ν²: O(1 + (L0R/ε)² + (L1R)²) → O(1 + L0R/ε + (L1R)^{4/3}) | L0²R²/ε² → L0R/ε and L1²R² → (L1R)^{4/3}. Never worse up to constants; speedup Θ((A² + C²)/(1 + A + C^{4/3})) | ℝ^d → any real inner-product space (minor) | min_k residual → last iterate | Needs R in the updates (EG needs only L0, L1). Only α = 1; no strongly monotone or weak-Minty results |
| Greenberg–Loizou, past-EG, [arXiv:2610.16886v1](https://arxiv.org/abs/2610.16886) Cor 3.3 (preprint, 2026-10-12). Prior. | O(1 + (L0R/ε)² + (L1R)²) for the min-iterate residual → same as above | Same as row 1 | None | min_k residual → last iterate | Same as row 1. PEG uses one new evaluation per step, a constant factor only |
| Repository [AnchoredGeneralizedMonotone](../../LongTails/Theorems/AnchoredGeneralizedMonotone.lean) (commit bf9edbc, 2026-10-03; not in the literature) | Takes G ≥ ‖F(x0)‖ as an input. Over this class G ≤ 2L0R·e^{2L1R} ([root_growth](../../LongTails/Proofs/MonotoneRadialSupport.lean)), giving O(1 + L0R/ε + (L1R)²) → O(1 + L0R/ε + (L1R)^{4/3}) | Worst case (L1R)² → (L1R)^{4/3}. Gain when L1R ≥ 1 and L0R/ε ≤ (L1R)²; speedup Θ((L1R)^{2/3}) when L0R/ε ≤ (L1R)^{4/3} | Requires an initial-residual input G → requires only R | None | Worse when G is small: if log(1 + L1GR/ε) = O(log(2 + L1R + L0R/ε)), the old bound O(1 + L0R/ε + L1R·log(…)) is better. The old updates do not need R |
| Center-of-gravity cuts with an extragradient cut at step 1/(2L), where L = L0 + 4L0L1R·e^{4L1R}. Standard reduction, finite d only; sketch checked here, not formalized | O(d·(1 + L1R + log(1 + L0R/ε))) → O(1 + L0R/ε + (L1R)^{4/3}) | Not uniform. The new bound wins when d ≥ (L1R)^{1/3} and L0R/ε ≤ d·L1R. It loses for d < (L1R)^{1/3}, or when L0R/ε ≫ d(L1R + log(L0R/ε)) | Finite d → any inner-product space, dimension-free | None (cuts return the observed best query point) | Cutting planes also need R (initial ball) and L0, L1 (cut step), and centroids are computationally expensive. The new method is cheap per step |

**Reduction check.** Substituting the growth bound into the anchored or EG theorems, or using Tikhonov regularization, gives (L1R)², not (L1R)^{4/3}.

**The new mechanism.**
- For ‖F(x)‖ ≥ 8L0R·e^{2L1t}, [large_residual_alignment](../../LongTails/Proofs/MonotoneRadialSupport.lean) shows ⟨F x, x − x*⟩ ≥ t‖F x‖/2. This is the classical local-boundedness inequality for monotone operators, applied at the comparison point x* + tF(x)/‖F(x)‖.
- Taking t = (L1R)^{1/3}/L1 allows long normalized steps.
- The step count (L1R)^{4/3} is then balanced against the log-threshold cost L1R·(L1R)^{1/3} of the reused anchored finish.

The proof ancestry is FEG/EAG anchoring, through the repository's step-adaptive anchored extragradient. That method supplies the finish; the warm phase and the balancing are new.

A gradient-only special case (F = ∇f) is not a direct competitor. Tyurin's accelerated method ([arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884) Thm 4.3) bounds the function gap, and its L1R·log(L1²Δ/L0) term is also order (L1R)² when only R is known.

**Search coverage.** On 2026-10-29 I searched arXiv, NeurIPS/ICML pages and the (L0, L1) VI/minimization literature. I read the theorem statements of 2510.22421 and 2610.16886. I did not read the full rate of Yoon et al.'s PolyakEG ([2609.26581](https://arxiv.org/abs/2609.26581)); the earlier repository review reports O(A² + C²). I found no monotone residual bound that avoids an initial-residual parameter at better than (L1R)², and no lower bound on the L1R term. The result was introduced in commit 2eb401c (2026-10-29), so there is no later work. The note's citations match what I checked. I did not run builds or axiom audits.

## Conclusion

**Yes. When only a radius bound is known, the proved worst-case residual complexity is better than every published dimension-free guarantee I found.**

The strongest published baseline is Choudhury–Loizou's extragradient analysis (Thm 3.6). The strongest dimension-free bound overall is the repository's own anchored method, once its initial-residual input is replaced by the worst case allowed by the growth bound.

| | F-evaluations for ‖F(x)‖ ≤ ε |
|---|---|
| EG / past-EG (published) | O(1 + (L0R/ε)² + (L1R)²) |
| Anchored, worst-case G (repository) | O(1 + L0R/ε + (L1R)²) |
| This result | O(1 + L0R/ε + (L1R)^{4/3}) |

Against the anchored bound, the gain is a factor of order (L1R)^{2/3} when L1R ≥ 1 and L0R/ε ≤ (L1R)^{4/3}. It vanishes when L0R/ε ≥ (L1R)². It loses when the actual initial residual is small. In fixed low dimension it also loses: centroid cutting planes cost O(d(L1R + log(L0R/ε))), so the new bound wins only when d ≥ (L1R)^{1/3} and L0R/ε ≤ d·L1R.

The comparison establishes a polynomial gain in the curvature term. The literature search supports priority but cannot prove it. No lower bound shows that (L1R)^{4/3} is optimal, and the method needs R in its updates.

What can be claimed is the first checked dimension-free subquadratic L1R transient for monotone (L0, L1)-Lipschitz residual minimization without an initial-residual bound. It comes from a simple but apparently new long-step warm phase.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
