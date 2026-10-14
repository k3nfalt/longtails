# Novelty assessment: `AcceleratedConvex`

**Guarantee.** For a convex, differentiable `f` on a real Hilbert space with an `L`-Lipschitz gradient oracle and a minimizer `xstar` satisfying `‖x0 − xstar‖ ≤ R`, the [theorem](../../LongTails/Theorems/AcceleratedConvex.lean) shows that Nesterov's method [`accelerated`](../../LongTails/Algorithms/Accelerated.lean) uses at most `K = max(1, ⌈√(2LR²/ε)⌉)` gradient calls. Its last iterate `x_K` satisfies `f(x_K) − f(xstar) ≤ ε` deterministically, almost surely for every oracle seed ([setup](../../LongTails/Setups/SmoothAndConvex.lean)).

**Complexity.** Here L is the smoothness constant, R bounds the initial distance to a minimizer, and ε is the target objective gap. The cost is

  `K = max(1, ⌈√(2LR²/ε)⌉) = O(1 + √(LR²/ε))` gradient calls, with no logarithmic factors and no restriction on dimension.

The method uses the standard estimate-sequence/linear-coupling form: `A_k = k(k+1)/4`, `a_k = (k+1)/2`, `y_k = (A_k x_k + a_k z_k)/A_{k+1}`, `x_{k+1} = y_k − ∇f(y_k)/L`, and `z_{k+1} = z_k − (a_k/L)∇f(y_k)`. It needs to know L but not R. The proof establishes the potential bound `A_K (f(x_K) − f*) ≤ (L/2)‖x0 − x*‖²`, so `f(x_K) − f* ≤ 2LR²/(K(K+1))` ([proof](../../LongTails/Proofs/AcceleratedConvex.lean)). Because the setup asks for gradients that hold for every seed, the oracle is forced to be deterministic.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nesterov (1983), *Soviet Math. Dokl.* 27; potential-function form in d'Aspremont–Scieur–Taylor, [*Acceleration Methods*](https://arxiv.org/abs/2101.09545) (FnT Optim. 5, 2021; arXiv v4 2024), Alg. 11, Thm 4.8, Cor. 4.9 | `⌈√(2LR²/ε)⌉` (from `f(x_N)−f* ≤ 2LR²/N²`) → `max(1,⌈√(2LR²/ε)⌉)` | None: same order, and essentially the same constant. The `K(K+1)` denominator is negligibly tighter. | None. The source is stated on ℝᵈ, but its argument is dimension-free and transfers verbatim to Hilbert spaces. | None: both bound the same last iterate `x_N` and both need L. | Uses a slightly smaller `A_k` sequence (`k(k+1)/4` instead of the greedy recursion); there is no other difference. |
| Beck–Teboulle (2009), FISTA, *SIAM J. Imaging Sci.* 2(1), Thm 4.4, with the nonsmooth part set to `g = 0` | `⌈√(2LR²/ε)⌉ − 1` (from `2LR²/(k+1)²`) → `max(1,⌈√(2LR²/ε)⌉)` | Worse by at most one call. | None; FISTA also covers composite objectives. | None. | None. |
| Kim–Fessler OGM, [Math. Program. 159 (2016)](https://arxiv.org/abs/1406.5468); bound stated in AST Cor. 4.6 | `⌈√(LR²/ε)⌉ − 1` (from `LR²/(N+1)²`) → `max(1,⌈√(2LR²/ε)⌉)` | Worse by a factor of about √2 for all `LR²/ε ≫ 1`. | None. | None: both are last-iterate bounds and both need L. | None. |
| Repository: [`GdConvex`](../../LongTails/Theorems/GdConvex.lean) (same setup) | `⌈LR²/(2ε)⌉` → `max(1,⌈√(2LR²/ε)⌉)` | A gain within the repository only: about a `√(LR²/ε)/(2√2)` speedup, which exceeds 1 when `LR²/ε > 8`. | None. | None. | None. |

**Reduction and mechanism check.** The Lean proof is exactly the three-inequality weighted sum in AST Thm 4.8 (convexity at `x*` and at `x_k`, plus the descent lemma), using the admissible weights `a_k² ≤ A_{k+1}`. There is no new mechanism; the result is the textbook theorem itself, not a corollary that needs an extra reduction. In the high-dimensional regime (`d ≥ N+1`), Drori's lower bound (2017, Thm 3; AST Thm 4.7) shows that OGM's `≈ √(LR²/ε)` calls are exactly optimal. This result therefore cannot be improved by more than a factor of about √2.

**Search coverage.** On 2026-10-07 I searched arXiv and journal sources on accelerated and optimized gradient methods for smooth convex minimization. I read the AST monograph's Thms 4.7–4.8 and Cors 4.6 and 4.9 directly. I took the Beck–Teboulle Thm 4.4 statement from citing sources, because text extraction failed on the only PDF I obtained (the companion IEEE TIP 2009 paper). There is no companion note. Git history shows the theorem was introduced on 2026-09-17/18 (`454f202`, `05e7e0a`), decades after all baselines.

## Conclusion

**No, this result does not improve complexity or cover new instances; it is a formalization of Nesterov's 1983 accelerated gradient method.**

The strongest baseline is the optimized gradient method of Kim and Fessler (2016), which applies to the same class: convex functions with L-Lipschitz gradients, an initial distance bound R, and a last-iterate objective gap.

| Method | Gradient calls for `f(x_N) − f* ≤ ε` |
|---|---|
| This result (Nesterov) | `max(1, ⌈√(2LR²/ε)⌉)` |
| Nesterov 1983 / AST Cor. 4.9 | `⌈√(2LR²/ε)⌉` |
| OGM (Kim–Fessler 2016) | `≈ √(LR²/ε)` |

The Lean bound matches the classical Nesterov bound and is about √2 worse than OGM. In sufficiently high dimension, Drori's lower bound makes OGM's count exactly optimal among first-order methods. The proof is the standard potential-function argument presented in d'Aspremont–Scieur–Taylor (Thm 4.8). The output (last iterate), the information required (L), and the assumptions all coincide with the classical results.

The only legitimate claims are a machine-checked proof in Lean and, within this repository, an improvement over the gradient-descent bound `⌈LR²/(2ε)⌉`; neither is new mathematics.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
