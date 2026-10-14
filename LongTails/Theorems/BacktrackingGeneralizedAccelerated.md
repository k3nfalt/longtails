# Backtracking acceleration needs no parameters under (L0, L1)-smoothness

Lean files: theorem [`BacktrackingGeneralizedAccelerated.lean`](BacktrackingGeneralizedAccelerated.lean), setup
[`../Setups/GeneralizedSmoothParameterFree.lean`](../Setups/GeneralizedSmoothParameterFree.lean), algorithm
[`../Algorithms/BacktrackingAccelerated.lean`](../Algorithms/BacktrackingAccelerated.lean), proofs
`../Proofs/BacktrackingAccelerated{Step,Count,Budget}.lean`.

## Setup

`E` is a real Hilbert space of any dimension and `f : E → ℝ` is

- convex and differentiable, with a differentiable gradient map satisfying the (L0, L1) condition of Zhang, He, Sra and
  Jadbabaie ([ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS)), `‖∇²f(x)‖ ≤ L0 + L1‖∇f(x)‖` for all `x`
  (`L0 > 0`, `L1 ≥ 0`);
- minimized at some `x*` with `‖x0 − x*‖ ≤ R` and `f(x0) − f(x*) ≤ Δ`.

These are exactly the assumptions of the repository setup `GeneralizedSmoothAndConvex` and of the closest papers below. The
oracle returns `∇f(x)` at a queried point; the cost is the number of queries. Success means `f(x̂) − f(x*) ≤ ε`.

**Information.** The algorithm is built from the public input `(E, x0, h0)` only, where `h0 > 0` is an arbitrary initial trial
step. `L0, L1, R, Δ, ε` are fields of `Params` but not of `Public`, so the Lean types guarantee that the method never uses them;
they appear only in the budget. No function values are queried.

Typical instances with interacting coordinates in any dimension: Poisson-type regression
`f(x) = Σ_j exp((Bx)_j) − (Bx)_j` with a dense design `B`, sums of exponentials `Σ_i exp(⟨a_i, x⟩ − b_i)` with a minimizer,
`‖Ax − b‖_p^p` with `p > 2`. For such objectives no global Lipschitz constant of the gradient exists, and the constants
`L0, L1, R` are rarely known.

## Algorithm

Nesterov's accelerated gradient method in similar-triangles form with backtracking on the step, where the acceptance test uses
gradients only. State `(A, x, v, h)`, initially `(0, x0, x0, h0)`. One trial makes two gradient calls:

    a  = (h + √(h² + 4hA))/2            (the root of a² = h(A + a))
    y  = (A x + a v)/(A + a),   g  = ∇f(y)          (call 1)
    x⁺ = y − h g,               g⁺ = ∇f(x⁺)         (call 2)
    if ⟨g⁺, g⟩ ≥ ‖g‖²/2:   (A, x, v, h) ← (A + a, x⁺, v − a g, 2h)     (accept)
    else:                  h ← h/2                                      (reject)

The output is the current `x`. There are no restarts, no phases and no horizon; the method is anytime. By convexity the test
implies the descent inequality `f(x⁺) ≤ f(y) − (h/2)‖g‖²`, which is all the estimate-sequence argument needs.

The scheme itself is classical: it is the backtracking fast gradient method of Nesterov
([Math. Program. 2013](https://doi.org/10.1007/s10107-012-0629-5), [universal gradient methods, 2015](https://doi.org/10.1007/s10107-014-0790-0)),
with the function-value descent test replaced by a gradient-only test; the test holds whenever `‖g⁺ − g‖ ≤ ‖g‖/2`, a
relative-error condition.
The contribution is its analysis under (L0, L1)-smoothness.

## Guarantee

For every valid instance the point held after

    budget = 2 ⌈ 5 + 4 √(32 L0 R²/ε)
                 + 26 (1 + L1 R) · log(1 + (2 + 13 L1 R)² (2 + 1/(64 L0 h0) + 16 L0 h0 + 5 L1² Δ/(4 L0) + 80 L1² Δ h0)) ⌉

gradient calls satisfies `f(x̂) − f(x*) ≤ ε` (`theorem result : Convergence spec budget`). In order notation,

    O( √(L0 R²/ε) + (1 + L1 R) · log(2 + L1 R + 1/(L0 h0) + L0 h0 + L1²Δ/L0 + L1²Δ h0) ).

The logarithm does not depend on `ε`; there is no factor `exp(L1 R)`; the initial step `h0` enters only logarithmically (and
both too small and too large values are allowed). Every gradient call, including those of rejected trials, is counted.

## What is new, and what is not

The leading term `√(L0 R²/ε)` is **not** new: it is optimal already for `L1 = 0`, it was obtained with known parameters by
Tyurin and by Vankov et al., and adaptively by GRAAL. What is new is the combination *no problem parameter supplied* and
*start-up cost linear in `L1 R` up to an ε-free logarithm*, with a restart-free first-order method.

| source | gradient calls for `f − f* ≤ ε` (constants dropped) | supplied to the method |
|---|---|---|
| Gorbunov et al. ([arXiv:2409.14989](https://arxiv.org/abs/2409.14989), ICLR 2025), accelerated method | leading term multiplied by a factor exponential in `L1 R` | `L0, L1` |
| Vankov et al. ([arXiv:2410.10800v3](https://arxiv.org/abs/2410.10800), ICLR 2025), Thm 6.2 (AGMsDR) | `√(L0R²/ε) + (L1R)^{2/3} log(F0/ε)` iterations, each with an exact one-dimensional search | `L0, L1` in the step rule, line-search oracle |
| Tyurin ([arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884), ICML 2026), Thm 4.3 | `√(L0R²/ε)` + start-up about `L1 R` times logarithms | `ℓ` (i.e. `L0, L1`), a distance bound, `Γ0 ≥ 2Δ/R²` |
| GRAAL ([arXiv:2507.09823v2](https://arxiv.org/abs/2507.09823), ICLR 2026), Cor. 3 | `1 + √(L0D²/ε) + (L1D)³ + (1 + (L1D)²) log(1/(η0 L0))` | initial step `η0`; `D = O(R)` needs `η0 L0 exp(L1 R) ≤ 1` |
| DADA ([arXiv:2501.10258v2](https://arxiv.org/abs/2501.10258), ICLR 2026), Cor. D.19 | `(L0R̄²/ε + L1²R̄²)` times logarithms (not accelerated) | `r0` |
| this repository, `GeneralizedAcceleratedConvex` / `CompositeGeneralizedAccelerated` | `√(L0R²/ε) + (L1R)^{2/3} log(Δ/ε)` / `√(L0R²/ε) + (1 + L1R) log(…)` | `L0, L1, R, Δ` |
| **this theorem** | `√(L0R²/ε) + (1 + L1R) · log(ε-free)` | nothing (`h0 > 0` arbitrary) |

The closest baseline is GRAAL, which is already adaptive, searchless and has the optimal leading term; relative to it the gain
is the start-up term, `(L1 R)³` → `(1 + L1 R)·log`, for an arbitrary `h0`, at the price of backtracking. Relative to Tyurin's
Theorem 4.3 the bound has the same shape and the method needs none of its inputs.

**Where this result is worse.** (i) It is not searchless: an accepted step costs two gradient calls and every rejection two
more; the budget counts about four calls per accepted step. (ii) With known `L0, L1` the start-up `(L1R)^{2/3}·log(1/ε)` of Vankov
et al. and of this repository's `GeneralizedAcceleratedConvex` has a better power of `L1 R` (with an ε-dependent logarithm).
(iii) The logarithm is ε-free but not constant: because `Δ` can be as large as `(L0/L1²)·exp(L1 R)`, it can be of order
`L1 R`, so in the worst case the start-up term is of order `(L1 R)²` (the same is true of the logarithms in the known-parameter
bounds of Tyurin and of this repository). Whether `L1 R·log` is the right start-up cost is open; no lower bound is claimed.
(iv) Unconstrained problems, exact gradients, the Hessian form of the (L0, L1) condition.

**Standard reductions that do not give the bound.** Treating `f` as smooth on the ball `B(x*, R)` and applying backtracking
FISTA theory gives a leading constant of order `L0·exp(c L1 R)`. GRAAL with a tiny initial step gives the `(L1R)³` start-up.
Guess-and-double on `R, L0, L1` for the known-parameter methods needs restarts and loses logarithms in `1/ε`. Monotone
(non-increasing) backtracking keeps the first, pessimistic step and puts `L1²Δ` into the leading term. AGMsDR with an inexact
Armijo search in place of its exact line search is not covered by the published analysis; Vankov et al. list removing the line
search as open.

## Mechanism

1. *Potential.* `A(f(x) − f*) + ½‖v − x*‖²` does not increase at accepted steps (the classical estimate-sequence computation,
   using only the accepted test and convexity). Hence `‖v − x*‖ ≤ R`, `‖x − x*‖ ≤ R` and `f(x) − f* ≤ R²/(2A)`.
2. *Self-bounding.* `‖∇f(x)‖² ≤ 8(L0 + L1‖∇f(x)‖)(f(x) − f*)`, so `L1‖∇f(x)‖ ≤ L0 + 5L1²R²/A` along the run.
3. *The test discovers the growth cap.* With `σ = 2 + 13 L1 R`: once `A > 0`, every trial with
   `h ≤ min(1/(32 L0), 2A/σ²)` is accepted, because then `‖y − x‖ ≤ (a/(A+a))·2R ≤ 3R/σ`, the gradient at `y` is controlled by
   the gradient at `x` (Grönwall), and `4(L0 + L1‖∇f(y)‖)h ≤ 1`. So the accepted step is never below
   `θ(A) = min(1/(64 L0), A/σ²)`. The threshold is proportional to `A` itself: this is the cap `a/A ≲ 1/(L1 R)` that
   known-parameter methods impose by hand, found here by the gradient test.
4. *Two growth regimes.* While `A < σ²/(64 L0)`, each accepted step multiplies `A` by at least `1 + 1/σ` (geometric start-up,
   `(1 + σ)·log` steps). Afterwards `√A` grows by at least `1/(16√L0)` per accepted step (the accelerated regime).
5. *Counting.* The trial step equals `h0·2^{accepts − rejections}` and is bounded below, so
   `trials ≤ 2·accepts + log₂(h0/h_min)`; each trial is two calls.

The proof step that has no counterpart for globally smooth functions is 3–4: the admissible step depends on the state of the
estimate sequence, not on a constant.

## Formal statement

`spec` has `Public = (E, x0, h0)`, `Params = Public + (L0, L1, R, Δ, ε)`, `valid`: all of `h0, L0, R, Δ, ε` positive and
`L1 ≥ 0`. `admissible` requires convexity, that every oracle reply is the gradient, differentiability of the gradient map with
the Hessian bound, and a minimizer within distance `R` and gap `Δ` of `x0`. `successful` asks for a minimizer `x*` with
`f(output) − f(x*) ≤ ε` almost surely (the algorithm and the oracle are deterministic). `Convergence spec budget` then states
that the algorithm, a function of the public input alone, succeeds within `budget` oracle calls for every valid parameter and
admissible instance.
