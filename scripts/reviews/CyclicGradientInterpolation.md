# CyclicGradientInterpolation: novelty assessment

The [theorem](../../LongTails/Theorems/CyclicGradientInterpolation.lean) ([setup](../../LongTails/Setups/InterpolatedFiniteSum.lean), [algorithm](../../LongTails/Algorithms/CyclicGradient.lean)) shows that fixed-order cyclic incremental gradient with full step 1/L returns, after `m⌈m³LR²/ε⌉` component-gradient calls, a last-pass iterate whose average gap `(1/m)Σᵢ(fᵢ(x)−fᵢ(x*))` is at most ε. This holds for every outcome, for m ≥ 1 convex, differentiable components with L-Lipschitz gradients on a real Hilbert space that share a minimizer x* with ‖x₀−x*‖ ≤ R.

**Complexity:** `N = m⌈m³LR²/ε⌉ = O(m + m⁴LR²/ε)` exact component-gradient calls, with N = 0 when R = 0. Here m is the number of components, L the per-component smoothness constant, R the initial distance and ε the accuracy. The updates use m, L and x₀; the stopping rule also needs R and ε. The setup's `allowedAlgorithm` allows only this method. Since x* minimizes F = (1/m)Σfᵢ, the criterion is exactly F(x)−F*.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nesterov acceleration/FISTA on F ([Beck–Teboulle 2009, Thm 4.4](https://doi.org/10.1137/080716542); repository [AcceleratedConvex](../../LongTails/Theorems/AcceleratedConvex.lean)) | `m·max(1,⌈√(2LR²/ε)⌉)` → `m⌈m³LR²/ε⌉` | Worse: by a factor of about m³√(LR²/ε) when LR²/ε ≥ 2. When LR²/ε < 2, both are O(m). | None. Its class is broader because it does not require interpolation. | None. Both are deterministic, return a final iterate and need known L. | The current method needs a common minimizer. Each accelerated step batches m calls; there is no line search or restart. |
| Repository [AcceleratedFiniteSumConvex](../../LongTails/Theorems/AcceleratedFiniteSumConvex.lean) (variance-reduced acceleration) | `O(m log log m + √(mLR²/ε))` in expectation → `O(m + m⁴LR²/ε)` deterministic | Worse in rate. Not directly comparable because the baseline bounds the expected gap. | None. The baseline does not require interpolation. | Expected gap → bound for every outcome; that difference is the current result's only edge. | The baseline uses randomized sampling. |
| [Cai–Diakonikolas, arXiv:2403.06873 v2, Thm 2.3](https://arxiv.org/html/2403.06873v2) (ICLR 2025), cyclic IGD with η ≤ 1/(√β·mL) and σ* = 0 | `O(m + mLR²√log(2+LR²/ε)/ε)` → `O(m + m⁴LR²/ε)` | Worse by m³, except that the current bound drops the √log factor. It wins only when log(2+LR²/ε) > m⁶. | Interpolation is required here but not there. Hilbert space here versus finite dimension there. The classes are incomparable. | Step tuned to the horizon → fixed step 1/L. Both give last-iterate guarantees and need R and ε for stopping. | The full step is a different method, not a complexity gain. |
| Special case: projections, fᵢ = (L/2)dist²(·,Cᵢ), m ≥ 3 ([Evron et al., ICML 2023, Prop 4.13](https://arxiv.org/abs/2306.03534)) | `O(m + m⁴L²R⁴/ε²)` (from max dist² ≤ 2m²R²/√k) → `O(m + m⁴LR²/ε)` | Same cyclic method: ε⁻² → ε⁻¹ when ε < LR². Simultaneous projections with acceleration (row 1) still give O(m√(LR²/ε)). | Squared-distance losses → general smooth interpolating losses; the old class is contained in the new one. | Max over sets → average; the projection case is argued only in the note, not in Lean. | Comparison holds only on the projection subclass. |

**Standard-reduction check.** Applying acceleration to the average needs only the facts that F is convex and L-smooth and that x* minimizes F. That reduction beats the selected budget for every LR²/ε ≥ 2 and stays within a factor of 2 below that threshold. So no complexity advantage remains on the target class, not even in a boundary regime. The genuinely new item is a method-specific analysis. It is a potential that couples the online loss to the squared displacement per pass ([CyclicGradientRun](../../LongTails/Proofs/CyclicGradientRun.lean)) and gives a universal O(1/K) last-iterate rate for the full-step cyclic method, including cyclic projections onto three or more nonlinear convex sets. Proof ancestry: Fejér monotonicity and firm nonexpansiveness are classical, and [Reich–Zalas](https://arxiv.org/abs/2205.13843) give only o(k^(−1/2)) residual estimates for general convex sets. Neither supplies the coupling.

**Search coverage (2026-10-07 UTC).** I searched arXiv, ICML/ICLR/NeurIPS proceedings and the cyclic-projection literature. I checked Evron 2023 Prop 4.13 and Beck–Teboulle Thm 4.4 in full text, and the statement of Cai–Diakonikolas Thm 2.3 in its HTML version. A 2026 continual-learning paper ([arXiv:2606.30559](https://arxiv.org/abs/2606.30559)) gives only local linear rates under regularity (abstract only). I found no earlier or later universal O(1/K) bound for full-step cyclic projections onto three or more sets, but older fixed-point sources may use different terminology. Git introduces the result at 2c23917 (2026-10-03). The companion note's statement matches the Lean theorem and openly says the result is not a complexity improvement. A previous repository review (`scripts/reviews/`) concluded SUBSTANTIVE; the user-reviewed `negative_examples.md` overrides it, and my comparison agrees with the correction. No build was run.

**Conclusion**

**No: on its own problem class, the result is slower than standard methods; what is new is an analysis of one specific method.**

The strongest baseline is Nesterov acceleration (FISTA) applied to the average F = (1/m)Σfᵢ. It uses the same component-gradient oracle and returns a deterministic final iterate. It does not even need the common-minimizer assumption.

| | component-gradient calls |
|---|---|
| Accelerated gradient on F | `O(m + m√(LR²/ε))` |
| This theorem (cyclic, step 1/L) | `O(m + m⁴LR²/ε)` |

For LR²/ε ≥ 2, the selected budget is worse by about m³√(LR²/ε). Below that threshold, both bounds are O(m). Against cyclic baselines, the bound beats Evron et al.'s ε⁻² bound only on the projection subclass. It beats Cai–Diakonikolas's small-step bound only when log(LR²/ε) > m⁶. Neither gain survives comparison with acceleration.

What appears new is a universal O(1/K) last-iterate rate for the full-step cyclic method, including exact cyclic projections onto three or more general convex sets. That is a mathematically interesting statement about a classical algorithm. However, the literature search cannot rule out an older equivalent estimate. The claimable contribution is this method-specific convergence analysis, not a better complexity for convex interpolating finite sums.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
