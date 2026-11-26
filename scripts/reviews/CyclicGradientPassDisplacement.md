# CyclicGradientPassDisplacement: novelty assessment

The [theorem](../../LongTails/Theorems/CyclicGradientPassDisplacement.lean) (setup [InterpolatedFiniteSum](../../LongTails/Setups/InterpolatedFiniteSum.lean), algorithm [cyclicGradient](../../LongTails/Algorithms/CyclicGradientPassDisplacement.lean)) proves that fixed-order cyclic component-gradient steps of size exactly `1/L`, stopped at a pass boundary, make the average objective gap `(1/m)Σᵢ(fᵢ(x_K) − fᵢ(x*)) ≤ ε` for every seed.

**Complexity.** The proved budget, counted in component-gradient calls, is `min{m⌈m³u⌉, m(1+⌈2B^{3/2}u/m⌉)}` with `u = LR²/ε` and `B = 1+m(m−1)`. Since `B^{3/2} ≤ m³`, this simplifies to

**N = 0 if LR² ≤ 2ε, and otherwise N = O(m³LR²/ε)** (the formula is also Θ of this for large `m`).

Here `m ≥ 1` is the number of convex, differentiable, `L`-smooth components on a real Hilbert space; they share a minimizer `x*`, `‖x₀ − x*‖ ≤ R`, and the oracle returns exact gradients. The setup fixes the order, step, and output through `allowedAlgorithm`, and the theorem proves compliance by `rfl`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [CyclicGradientInterpolation](../../LongTails/Theorems/CyclicGradientInterpolation.lean) (same setup and method; prior, Git 2c23917) | O(m + m⁴LR²/ε) → 0 or O(m³LR²/ε) | Factor ≈ m/2 when m ≥ 2 and LR² > 2ε. Zero calls replace one pass when LR² ≤ 2ε. `budget_le_existing` proves pointwise ≤ | None | None: same last pass-boundary iterate | None |
| [Cai–Diakonikolas, ICLR 2025, Thm 1](https://proceedings.iclr.cc/paper_files/paper/2025/file/fea9f93f4cec99f65a8b4d575fc353a8-Paper-Conference.pdf) / [arXiv Thm 2.3](https://arxiv.org/pdf/2403.06873): cyclic incremental gradient with step `1/(mL√β)` and σ*=0 | O(m + (mLR²/ε)√log(2+LR²/ε)) → O(m³LR²/ε) | Worse by m²/√log(2+LR²/ε). An asymptotic gain needs log(2+LR²/ε) ≫ m⁴; the previous repository threshold was m⁶ | Finite-dimensional → Hilbert space, but their class needs no interpolation, so the classes are incomparable | Horizon-tuned step → fixed step 1/L. Both give last iterates and need R, ε to stop | Interpolation assumption required |
| Repository [AcceleratedConvex](../../LongTails/Theorems/AcceleratedConvex.lean) applied to the average (m batched calls per step) | m·max{1,⌈√(2LR²/ε)⌉} → O(m³LR²/ε) | Worse: m√u → m³u for every LR² > 2ε. The selected method only wins the trivial range LR² ≤ 2ε, where returning x₀ suffices | None; selected additionally needs interpolation | None: known L, deterministic returned iterate | Same component oracle. AGD is excluded only by the setup's algorithm restriction |
| [Swartworth et al., NeurIPS 2023, Thm 1, Lemma 2](https://papers.nips.cc/paper_files/paper/2023/file/d72ae75abaa70a3b19c5d4f436c680d1-Paper-Conference.pdf), special case: subspace projections `fᵢ=(L/2)dist²(·,Cᵢ)` | O(m + m³LR²/ε) → same | None: same order | Linear subspaces → arbitrary smooth convex interpolating components (nested, broader) | None | The projection specialization is on paper only. For closed convex sets the same order follows from [Reich–Zalas, Lemma 3.1, (3.2)](https://arxiv.org/pdf/2205.13843) plus the repository's earlier displacement bound |

**Standard-reduction check.** I verified Reich–Zalas (3.2): `(1/m)Σ d(y_k,Cᵢ)² ≤ (m/2)‖y_k−y_{k−1}‖·d(y_{k−1},C)`. The new proof uses the same idea, "gap ≲ distance × pass displacement", for gradient steps: Fejér monotonicity gives `E_K ≤ 2r₀d_K`, and the existing potential gives `√(K(K−1))·d_K ≤ √B·r₀`. The repository's existing transfer inequality is then reused. The only new step is this ~100-line recombination of inherited estimates, with no new mechanism. Proof ancestry: Fejér/firm-nonexpansiveness arguments and the earlier [CyclicGradientRun](../../LongTails/Proofs/CyclicGradientRun.lean) potential. Neither supplies a complexity row by itself.

**Search coverage (2026-11-26 UTC).** I searched arXiv, ICLR, NeurIPS, and COLT for cyclic and incremental gradient methods under interpolation, last-iterate SGD at step `1/L`, continual-learning forgetting rates, and cyclic projections. This covered Evron et al. 2022/2023/2025, Attia et al. 2025, Schliserman–Koren 2026 (random draws, not a fixed order), and 2026 incremental-proximal work. I found no earlier theorem giving O(m³LR²/ε) for full-step cyclic GD on general smooth interpolating components. The result entered Git at 5dbcee00 (2026-11-26). The companion note matches the Lean statement and candidly concedes the projection-case derivability and the AGD gap. Its informal m³ lower bounds are unformalized and were not checked. No build or axiom audit was run.

## Conclusion

**No: this is a sharper analysis of a deliberately fixed slow method, not a better way to solve the problem.** The proof tightens the repository's own cyclic certificate by a factor of about m. Two stronger guarantees on the same component-gradient oracle are unaffected:

| Method | Calls for average gap ≤ ε |
|---|---|
| This theorem (cyclic, step 1/L) | O(m³LR²/ε) |
| Cai–Diakonikolas cyclic, smaller step | O(m + (mLR²/ε)√log(2+LR²/ε)) |
| AGD on the average | O(m + m√(LR²/ε)) |

AGD is better whenever LR² > 2ε. Cai–Diakonikolas analyze the same cyclic order and beat this theorem unless log(LR²/ε) ≫ m⁴, which is an astronomically small accuracy for any m ≥ 2. The user-reviewed assessment of the m⁴ predecessor already rated this setup NO IMPROVEMENT for the same reason, and removing one factor of m does not overturn it.

The m³ order is not new in the overlapping cases either. Swartworth et al. state it for subspace projections, and Reich–Zalas's inequality yields it for convex-set projections. What remains is extending that order to arbitrary smooth convex interpolating components at the full step 1/L. My search found no prior statement of that extension, but it is a short recombination of known estimates, and the literature search does not establish priority.

The contribution that can be claimed is a factor-m improvement in the certified complexity of full-step cyclic gradient descent under interpolation, with no new complexity, scope, or output advantage over applicable methods.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
