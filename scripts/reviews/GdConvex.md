# GdConvex: novelty assessment

[`result`](../../LongTails/Theorems/GdConvex.lean) proves the following. Let `f` be convex on a real Hilbert space `E` (any dimension) with an `L`-Lipschitz gradient, and suppose some minimizer `xstar` satisfies `‖x0 − xstar‖ ≤ R` ([setup](../../LongTails/Setups/SmoothAndConvex.lean)). Then the **last iterate** of plain gradient descent `x_{k+1} = x_k − (1/L)∇f(x_k)` ([algorithm](../../LongTails/Algorithms/Gd.lean)) satisfies `f(x_K) − f(xstar) ≤ ε` after `K = max(1, ⌈LR²/(2ε)⌉)` steps. The setup forces the oracle to be deterministic: all oracle answers equal the unique gradient, so the "almost surely" in the statement is trivial.

**Complexity** (exact gradient calls, one per iteration):

  N_GD = max(1, ⌈L R² / (2ε)⌉) = O(1 + L R²/ε).

Here `L` is the gradient-Lipschitz constant, `R` bounds the initial distance to a minimizer, and `ε` is the target objective gap. There are no logarithms. The proof ([Proofs/GdConvex.lean](../../LongTails/Proofs/GdConvex.lean)) uses the textbook argument: the descent lemma plus a three-point inequality are summed over iterations, then monotonicity gives `f(x_K) − f* ≤ L‖x0 − x*‖²/(2K)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Classical GD bound `f(x_N) − f* ≤ L‖x0 − x*‖²/(2N)` with step `1/L`, as quoted by Drori–Teboulle (§3, citing Nesterov's 2004 book and Beck–Teboulle 2009) | `⌈LR²/(2ε)⌉` → `max(1, ⌈LR²/(2ε)⌉)` | None: identical bound | None | None (same algorithm, same last-iterate output) | None |
| Drori–Teboulle, *Math. Program.* 145 (2014) 451–482, [arXiv:1206.3209](https://arxiv.org/abs/1206.3209), Thm 3.1 (tight by Thm 3.2): GD with step `h/L`, `0 < h ≤ 1`, has `f(x_N) − f* ≤ LR²/(4Nh + 2)`; with `h = 1` | `max(1, ⌈(LR²/ε − 2)/4⌉)` → `max(1, ⌈LR²/(2ε)⌉)` | Worse: about 2× more calls whenever `LR²/ε ≫ 1` | None. DT state the result on `ℝ^d`, but their proof uses only inner-product inequalities. I did not check that extension line by line. | None | The selected budget is not tight for this exact algorithm |
| Nesterov AGD; Bubeck, [arXiv:1405.4980](https://arxiv.org/abs/1405.4980) (Found. Trends ML 2015), Thm 3.19: `f(y_t) − f* ≤ 2L‖x1 − x*‖²/t²`. Also in the repository: [AcceleratedConvex](../../LongTails/Theorems/AcceleratedConvex.lean), same `spec`, same 2026-09-17 commit | `max(1, ⌈√(2LR²/ε)⌉)` → `max(1, ⌈LR²/(2ε)⌉)` | Worse: a factor of about `√(LR²/(8ε))` when `LR²/ε > 8`. When `LR²/ε ≤ 8`, both budgets are at most 4 calls. | None | None (both give a last-iterate guarantee and need `L`) | AGD keeps an extra momentum sequence. Its oracle and information requirements are the same. |

**Reduction check.** The result is the standard GD analysis, with a constant weaker than the tight 2014 bound, and no new mechanism is present. The only nonstandard elements are the general (possibly infinite-dimensional) Hilbert space and the Lean formalization. Neither changes the mathematics. Nesterov's lower bound (Bubeck Thm 3.14, `3L‖x1 − x*‖²/(32(t+1)²)` for `t ≤ (n−1)/2`) shows that AGD's `O(√(LR²/ε))` is optimal for this class in high or infinite dimension. The lower bound is a statement about the class, not specifically about GD.

**Search coverage.** On 2026-10-07 I checked Drori–Teboulle Thms 3.1–3.2 and Bubeck Thms 3.3, 3.14 and 3.19 in their full texts. I did not re-open Nesterov's book or Beck–Teboulle 2009 directly; the `LR²/(2N)` bound is cited through Drori–Teboulle's statement. There is no companion note. The theorem was introduced in commit 454f202 (2026-09-17), and every cited baseline predates it by more than a decade.

**Conclusion**

**No: this is the textbook gradient-descent rate, with a slightly worse constant than the best known analysis of the same method.**

For an `L`-smooth convex function with a minimizer within distance `R`, the theorem gives the following budgets:

| Method | Gradient calls for `f(x_K) − f* ≤ ε` |
|---|---|
| This result (GD, step 1/L) | `max(1, ⌈LR²/(2ε)⌉)` |
| Drori–Teboulle 2014, same GD | `≈ LR²/(4ε)` |
| Nesterov AGD (Bubeck Thm 3.19; repo AcceleratedConvex) | `max(1, ⌈√(2LR²/ε)⌉)` |

The `LR²/(2N)` bound has been classical for decades. Drori–Teboulle proved a tight bound for the same algorithm that needs about half as many calls. Nesterov's accelerated method, which uses the same oracle and the same parameter knowledge, needs only `O(√(LR²/ε))` calls. That is better whenever `LR²/ε > 8`; below that threshold, every method needs at most four calls.

The setup is not broader in any meaningful way: arbitrary Hilbert spaces are covered by the same proofs. The output (last iterate) and the information required (`L`, `R`, `ε`) are the same as in the baselines. The only contribution that can be claimed is a machine-checked formalization of a known textbook theorem.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
