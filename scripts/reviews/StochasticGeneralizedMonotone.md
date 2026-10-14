# Stochastic generalized-smooth monotone root finding: novelty assessment

The [theorem](../../LongTails/Theorems/StochasticGeneralizedMonotone.lean) shows that the confidence-selected output of [localized clipped extragradient](../../LongTails/Algorithms/LocalizedClippedExtragradient.lean) satisfies `P(‖F(X)‖ > ε) ≤ δ`. The [setup](../../LongTails/Setups/StochasticGeneralizedMonotone.lean) is a continuous monotone `F` on a finite-dimensional Hilbert space that is 1-symmetric `(L₀,L₁)`-Lipschitz and has a root within `R` of `x₀`. The oracle is unbiased, jointly measurable, and IID, with uniform variance `σ²`.

**Selected complexity** (from `total_calls_bound`; `ε>0`, `0<δ<1`; universal constant `2⁶⁰` suppressed):

    O( (1 + L₀R/ε + (L₁R)² + σ²/ε²) · log³(2 + L₀R/ε + L₁R) · log((2 + L₀R/ε + L₁R)/δ) )

Here `L₀,L₁` are the generalized-Lipschitz constants, `R` bounds `‖x₀−x⋆‖`, `σ²` is the variance, `ε` is the residual target, and `δ` is the failure probability. The algorithm needs `L₀,L₁,R,σ,ε,δ`, but no bound on the initial residual. All batches, the `⌈log₂(T/δ)⌉+1` repetitions, and padding are counted.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ji–Lan–Zhu, [arXiv:2609.04188](https://arxiv.org/abs/2609.04188) Thm 2.2 (v1 3 Sep 2026, prior; preprint), applied through **localization** to `B(x₀,2R)` with the local constant `L ≤ L₀e^{3L₁R}` (Grönwall from `F(x⋆)=0`) | `Õ(L₀e^{3L₁R}R/ε + (σ²/ε²)(L₁R + log(L₀R/ε))³)` for the expected (projected) residual → selected bound | Exponential → polynomial in `L₁R`. The curvature term drops from `e^{3L₁R}L₀R/ε` to `L₀R/ε + (L₁R)²`, and the cubic factor `(L₁R)³` on the variance term becomes `log³(L₁R)`. The gain is unbounded once `L₁R ≫ log(2+L₀R/ε)`. For `L₁R = O(1)` both bounds are the same order up to `log(1/δ)` | Global `L`-Lipschitz (eq. 1.2) → `(L₀,L₁)`-Lipschitz without paying an exponential local constant | Expected residual → high-probability `‖F(X)‖≤ε`, at a cost of `log(1/δ)` | Unconstrained only; JLZ also covers constrained VIs. The reduction still has two unverified steps: converting the projected residual to `‖F‖` near the ball boundary, and amplifying confidence. The `(L₁R)²` term and the extra log factors are a cost when `L₁=0` |
| Vankov–Nedić–Sankar, [arXiv:2410.12334v2](https://arxiv.org/abs/2410.12334) Thm 4.4 (prior; v2 Oct 2025) | `O(1/k)` bound on `E dist²(x_k,X⋆)` → selected bound | Not comparable: different accuracy criterion; requires `μ>0` | Quasi-sharpness `μ>0` (Asm 2.4) with `α≤1/2` for rates → general monotone with `α=1`. This newly covers operators such as a skew-plus-radial-penalty map, which have `⟨F(x),x⟩=0` near the root | Distance → residual | VNS also cover constrained and structured non-monotone problems |
| Repository [AnchoredGeneralizedMonotone](../../LongTails/Theorems/AnchoredGeneralizedMonotone.lean) (exact oracle only; special case `σ=0`) | `O(L₀R/ε + (1+L₁R)log(1+(L₀+L₁G)R/ε))` → `O((1+L₀R/ε+(L₁R)²)·logs)` | Worse at `σ=0`: `(L₁R)²` instead of `L₁R` | None | None (deterministic baseline is anytime last iterate) | The baseline needs an initial-residual bound `G` and an exact oracle; it gives no guarantee when `σ>0` |

**Reduction check.** Plain localization of the strongest prior method (JLZ) pays `e^{O(L₁R)}`, as shown in the first row. Running the deterministic anchored method with robust mini-batched calls is a plausible reduction whose error tolerance I did not verify. Even if it works, its cost is roughly the product `(L₀R/ε + L₁R·log)·(1+σ²/ε²)`, not a sum. The new ingredient is the stochastic clipped-extragradient contraction `E‖x⁺−p‖² ≤ (1−r/(4608S))‖x−p‖² + σ²/(64mS²)` (`one_step_integral`), which keeps variance additive while the step saturates. This is used inside JLZ-style accumulative regularization (proof ancestry). Metric-majority confidence boosting is standard median-of-means for points. I read the lemma statement but not the full proof, and did not rebuild the project.

**Search coverage** (8 Oct 2026). I searched arXiv and the ICML/NeurIPS/TMLR literature on stochastic VIs under generalized smoothness and on stochastic Halpern, anchored, and clipped extragradient methods: Gorbunov et al. 2022/23, Yoon–Loizou 2608.06182 and 2609.36033, VRAF 2609.35631, and JLZ. Every stochastic monotone residual result I found assumes global (often samplewise) Lipschitzness. I did not confirm the companion note's claim that VNS was accepted at TMLR, and I read JLZ Section 4 only through the note. The note's other claims agree with the Lean statement. The result was introduced in commit `f8dc088` (7 Oct 2026); the area is moving fast, so priority is uncertain.

**Conclusion**

**Yes—when `L₁R` is large, the proved total complexity is exponentially better than the best applicable prior route.** The strongest baseline is Ji–Lan–Zhu's accumulative regularization for globally Lipschitz stochastic VIs. It applies only after localizing to a ball where the Lipschitz constant can be as large as `L₀e^{3L₁R}`.

| | oracle calls for `‖F(X)‖ ≤ ε` |
|---|---|
| JLZ + localization | `L₀e^{3L₁R}R/ε + (σ²/ε²)(L₁R)³` (up to logs) |
| this result | `(L₀R/ε + (L₁R)² + σ²/ε²)·log³·log(1/δ)` |

The gain appears once `L₁R` exceeds a logarithm of `L₀R/ε`. If `L₁R=O(1)` the result only matches the known smooth order. In the exact-oracle case it is worse than the repository's anchored method, `L₁R` versus `(L₁R)²`. Prior stochastic results that do allow generalized smoothness require quasi-sharpness, so the result also covers monotone instances they exclude.

What is established is a comparison of proved upper bounds; no lower bound shows that the localized baseline really suffers `e^{L₁R}`. A careful inexact analysis of a deterministic generalized-smooth method could narrow the gap, but the obvious version multiplies the curvature and variance terms instead of adding them. The search found no prior stochastic residual guarantee polynomial in `L₁R`, but that does not establish priority.

The contribution that can be claimed is the first checked high-probability residual bound for finite-variance monotone `(L₀,L₁)`-Lipschitz operators with polynomial `L₁R` dependence and an additive variance term.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
