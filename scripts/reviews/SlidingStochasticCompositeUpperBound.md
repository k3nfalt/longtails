# Two-oracle sliding for nonconvex `f` + stochastic convex `h`: novelty assessment

[`result`](../../LongTails/Theorems/SlidingStochasticCompositeUpperBound.lean) proves the following ([setup](../../LongTails/Setups/SlidingStochasticComposite.lean), [algorithm](../../LongTails/Algorithms/SlidingStochasticComposite.lean)). Take `F = f + h` on a finite-dimensional Euclidean space, where `f` is `ℓ`-smooth and possibly nonconvex and `h` is convex and `L`-smooth. Oracle 0 returns exact `∇f`; oracle 1 returns unbiased IID stochastic `∇h` with variance at most `σ²`. Prox-linear sliding (an outer prox-linear step on `f`, with AC-SA solving each `ℓ`-strongly convex model) returns a uniformly random stage center `x̂` with `E[F(x̂) − inf_y{F(y) + ℓ‖y − x̂‖²}] ≤ ε²/(8ℓ)`.

**Complexity.** The parameters are: `ℓ > 0` (smoothness of `f`, which is also the weak-convexity scale of `F`), `L ≥ 0` (smoothness of `h`), `σ` (noise), `Δ ≥ F(x₀) − inf F`, and `ε > 0`. The proved budget gives:

- `∇f` calls: `⌈32ℓΔ/ε²⌉ + 1 = O(1 + ℓΔ/ε²)`
- `∇h` calls: `O((1 + ℓΔ/ε²)(√(1 + L/ℓ) + σ²/ε²))`

There are no logarithms. Since `Γ ≤ ‖∇F‖²/(2ℓ)`, the condition `E‖∇F‖² ≤ ε²/4` implies success. Single-oracle methods meeting that condition therefore qualify as baselines, with each joint call costing one `∇f` and one `∇h`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan RSG, [SIAM J. Optim. 23 (2013)](https://arxiv.org/abs/1309.5549), Cor. 2.2, applied to `F` (`(ℓ+L)`-smooth) with oracle `∇f + g` | Each of `∇f`, `∇h`: `(1+(ℓ+L)Δ/ε²)(1+σ²/ε²)` → `∇f`: `1+ℓΔ/ε²`; `∇h`: `(1+ℓΔ/ε²)(√(1+L/ℓ)+σ²/ε²)` | `∇f`: smaller by a factor of about `(1+L/ℓ)(1+σ²/ε²)`. `∇h`: the noise term `(ℓ+L)Δσ²/ε⁴ → ℓΔσ²/ε⁴`, and the deterministic term `(ℓ+L)Δ/ε² → √(ℓ(ℓ+L))Δ/ε²`. A gain when `L ≫ ℓ` or `σ ≫ ε`, and same order otherwise (when `ℓΔ ≥ ε²`) | None (same class) | Both use a random iterate. The criterion is a Moreau gap, implied by RSG's `E‖∇F‖²` | Uses two separate oracles, so `∇f` cannot be noisy. Weaker criterion than `‖∇F‖`: extracting a stationary point needs an extra prox solve, which is not proved |
| Allen-Zhu SGD4, [arXiv:1801.02982 v3](https://arxiv.org/abs/1801.02982) (NeurIPS 2018), Thm. 4: `ℓ`-bounded nonconvexity, `(ℓ+L)`-smooth `F` | Joint calls `(ℓ+L)Δ/ε² + σ²log³(1/ε)/ε² + ℓΔσ²/ε⁴` → as above | `∇f`: `ℓΔ/ε²` versus the whole joint bound. `∇h`: `(ℓ+L)Δ/ε² → √(ℓ(ℓ+L))Δ/ε²`, and the `log³` factor is removed. The noise term is the same order | None | SGD4 bounds `E‖G_F‖ ≤ ε` (first moment). This does not give `E Γ ≤ ε²/(8ℓ)` without a second-moment bound, so the comparison is approximate | SGD4 gives a near-stationary output with a stronger meaning. Its `Δ` is measured to a minimizer |
| Deterministic overlap `σ = 0`: inexact proximal point on `F`, each `ℓ`-strongly convex subproblem `F + ℓ‖·−c‖²` solved by Kovalev et al. sliding ([NeurIPS 2022, arXiv:2205.15136](https://arxiv.org/abs/2205.15136), §2.2; needs a convex sum and smooth `p`, `q`) | `∇f`: `(ℓΔ/ε²)·log(ℓΔ/ε²)`; `∇h`: `√(ℓ(ℓ+L))Δ/ε²·log(ℓΔ/ε²)` (my reduction: log from cold-start subproblem accuracy) → `1+ℓΔ/ε²`; `(1+ℓΔ/ε²)√(1+L/ℓ)` | Only a log factor on this overlap | Adds stochastic `∇h` (`σ > 0`) | None | The reduction's log factor comes from my derivation, not a published theorem. Kovalev et al. alone needs a convex total objective |

**Reduction check and mechanism.** The algorithm is inexact proximal-gradient descent (one `∇f` per step, `O(ℓΔ/ε²)` steps). Each prox subproblem is `ℓ`-strongly convex and `(ℓ+L)`-smooth with `σ²`-noisy gradients, and is solved by AC-SA (Ghadimi–Lan 2012), which needs `√(1+L/ℓ) + σ²/ε²` calls. The result is thus a direct composition of known theorems; the only detail I found beyond plain composition is that the inner initial distance is bounded by the stage gap, which avoids a log factor. Proof ancestry: Lan's gradient sliding ([1406.0919](https://arxiv.org/abs/1406.0919)) and Kovalev et al. supply the idea of skipping the expensive gradient, and AC-SA supplies the inner bound; none states this nonconvex two-oracle guarantee. Boundary checks: at `L = σ = 0` the budget is GD's `O(ℓΔ/ε²)`. As `ℓ → 0`, the target `ε²/(8ℓ)` becomes vacuous, so the result does not cover convex `f` in a meaningful way. If `Δ ≤ ε²/(8ℓ)`, then `x₀` already succeeds.

**Search coverage (2026-11-27).** I searched the web and arXiv for nonconvex, weakly convex and stochastic gradient sliding, and two-oracle nonconvex composites. I read Allen-Zhu Thm. 4 and Kovalev et al. §2.2 (through a partial HTML extraction; its theorem numbering is unverified). [Lan–Li–Xu 2412.14291 v3](https://arxiv.org/abs/2412.14291) (16 Nov 2026) needs a compact feasible set and a single oracle. Nonconvex conditional gradient sliding ([1708.04783](https://arxiv.org/abs/1708.04783)) uses a linear minimization oracle. Neither applies. I did not re-read Ghadimi–Lan Cor. 2.2 or check Lan's 2020 textbook. The result was introduced in commit `0ef763ac` (2026-11-27). The companion note's "first stated guarantee, no technical novelty" claim agrees with what I found, and its SGD4 citation checks out, although SGD4 uses a different criterion.

## Conclusion

**Yes, but modestly: it separates the two gradient counts in a way single-oracle methods cannot, and the proof is a routine composition.**

The strongest single-oracle baseline is Allen-Zhu's SGD4, which needs `(ℓ+L)Δ/ε² + σ²log³(1/ε)/ε² + ℓΔσ²/ε⁴` calls of each gradient. This result calls the expensive nonconvex gradient only as often as GD on `f` alone. It also slightly improves the cheap-oracle count:

| | `∇f` calls | `∇h` calls |
|---|---|---|
| SGD4 (joint) | `(ℓ+L)Δ/ε² + σ²log³/ε² + ℓΔσ²/ε⁴` | same |
| This result | `ℓΔ/ε²` | `ℓΔσ²/ε⁴ + √(ℓ(ℓ+L))Δ/ε² + √(1+L/ℓ) + σ²/ε²` |

The `∇f` gain is a factor of about `1 + L/ℓ + σ²/ε²` (for `ℓΔ ≥ ε²`), which is large when `L ≫ ℓ` or `σ ≫ ε`. The accuracy criterion is a Moreau gap, so SGD4's first-moment gradient-norm guarantee is not exactly comparable.

The mechanism is inexact proximal gradient on `f` with AC-SA prox solves. On the deterministic overlap, proximal point combined with Kovalev et al.'s sliding already gives the same counts up to a logarithm. I found no paper stating the stochastic two-oracle guarantee, but that is a search result, not proof of priority.

What can be claimed is a first explicit, log-free two-oracle bound for this natural class, built from standard pieces. It gains significance from the paired lower bound, which was not assessed here.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
