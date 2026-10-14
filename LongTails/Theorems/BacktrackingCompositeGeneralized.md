# Parameter-free accelerated composite optimization under (L0, L1)-smoothness

Lean files: theorem [`BacktrackingCompositeGeneralized.lean`](BacktrackingCompositeGeneralized.lean)
(`OracleTemplate.CompositeParameterFree.result`, budget `OracleTemplate.CompositeParameterFree.budget`), setup
[`../Setups/CompositeGeneralizedParameterFree.lean`](../Setups/CompositeGeneralizedParameterFree.lean), algorithm
[`../Algorithms/BacktrackingComposite.lean`](../Algorithms/BacktrackingComposite.lean) (`backtrackingComposite`), proofs
[`../Proofs/BacktrackingCompositeStep.lean`](../Proofs/BacktrackingCompositeStep.lean) (one trial),
[`../Proofs/BacktrackingCompositeRun.lean`](../Proofs/BacktrackingCompositeRun.lean) (thresholds, phases, rejection count),
[`../Proofs/BacktrackingCompositePotential.lean`](../Proofs/BacktrackingCompositePotential.lean) (growth and accuracy),
[`../Proofs/BacktrackingCompositeBudget.lean`](../Proofs/BacktrackingCompositeBudget.lean) (the public budget),
[`../Proofs/BacktrackingCompositeExecution.lean`](../Proofs/BacktrackingCompositeExecution.lean) (three calls per trial).

## Setup

The instance class and the oracle model are, word for word, those of the repository setup
[`CompositeGeneralizedSmooth`](../Setups/CompositeGeneralizedSmooth.lean) (theorem
[`CompositeGeneralizedAccelerated`](CompositeGeneralizedAccelerated.md)): minimize `F = f + ψ` over a convex set `Q ⊆ E`, `E` a
real Hilbert space of any dimension, where

- `f : E → ℝ` is convex with a continuous gradient satisfying the symmetric first-order (L0, L1) condition of Chen, Zhou, Liang
  and Lu ([ICML 2023](https://proceedings.mlr.press/v202/chen23ar.html)): if `‖∇f‖ ≤ M` on the segment `[x, y]` then
  `‖∇f(x) − ∇f(y)‖ ≤ (L0 + L1 M)‖x − y‖` (implied by `‖∇²f(x)‖ ≤ L0 + L1‖∇f(x)‖`, Zhang, He, Sra, Jadbabaie,
  [ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS));
- `ψ : E → ℝ` is convex on `Q` (constraints: `ψ ≡ 0`; regularizers: `Q = E`);
- a gradient query at `x` returns `∇f(x)`; a prox query `(a, z, v)` with `a > 0` returns a minimizer over `Q` of
  `‖u − z‖²/(2a) + ⟨v, u − z⟩ + ψ(u)` (Nesterov's composite gradient mapping,
  [Math. Program. 140, 2013](https://doi.org/10.1007/s10107-012-0629-5)); every query counts one call;
- some minimizer `x*` of `F` on `Q` satisfies `‖x0 − x*‖ ≤ R`, `F(x0) − F(x*) ≤ Δ`, `‖∇f(x*)‖ ≤ G`; `x0 ∈ Q`.

**Information model (the only change).** The public input is `(E, x0, h0)`, where `h0 > 0` is an arbitrary initial trial step.
`L0, L1, R, Δ, G, ε` are fields of `Params` but not of `Public`, so the Lean types guarantee that the method uses none of
them; they appear only in the call budget. In the repository's composite theorem the method is built from
`(E, L0, L1, R, Δ, x0)`: it needs the smoothness constants for its step rule, `R` for the step cap `a_k ≤ A_k/(1 + 32 L1 R)`
that keeps every query inside the trust region of the last observed gradient, and `Δ` for the start `A_0 = R²/(2Δ)`.

Success means that the returned point lies in `Q` and `F(x̂) − F(x*) ≤ ε`. The `valid` predicate requires
`h0, L0, R, Δ, ε > 0` and `L1, G ≥ 0`.

Instances with interacting coordinates in any dimension: ℓ1- or box-constrained Poisson regression `Σ_j exp((Bx)_j) − (Bx)_j`,
exponential-loss boosting `Σ_i exp(⟨a_i, x⟩ − b_i)` with a simplex or norm constraint, `‖Ax − b‖_p^p + λ‖x‖_1` with `p > 2`.
For such problems no global Lipschitz constant of `∇f` exists, `∇f(x*) ≠ 0` because of the constraint or regularizer, and
`L0, L1, R, Δ` are typically unknown or only known as loose upper bounds; a loose `R` inflates the step cap `1/(1 + 32 L1 R)`
and a loose `Δ` shrinks `A_0` in the known-parameter method.

## Algorithm

State `(A, x, z, h)`, initially `(0, x0, x0, h0)`. One *trial* makes three oracle calls:

    a  = (h + √(h² + 4hA))/2                 (the root of a² = h(A + a); a = h when A = 0)
    y  = (A x + a z)/(A + a),  g  = ∇f(y)                         (call 1)
    p  = prox(a, z, g)                                             (call 2)
    x⁺ = (A x + a p)/(A + a),  g⁺ = ∇f(x⁺)                        (call 3)
    if 2h⟨g⁺ − g, x⁺ − y⟩ ≤ ‖x⁺ − y‖²:  (A, x, z, h) ← (A + a, x⁺, p, 2h)      (accept)
    else:                                h ← h/2                               (reject)

The output is the current `x`. This is, up to the form of the estimate sequence, Nesterov's accelerated method for composite
problems with backtracking on the step ([Math. Program. 140, 2013](https://doi.org/10.1007/s10107-012-0629-5); the
backtracking condition there is checked with the gradient at the new point, see Scheinberg–Goldfarb–Bai,
[Found. Comput. Math. 2014](https://doi.org/10.1007/s10208-014-9189-9), and Florea–Vorobyov,
[arXiv:1612.02352](https://arxiv.org/abs/1612.02352), Table 3), written in similar-triangles form; the
acceptance test is gradient-based, since by convexity it implies
`f(x⁺) ≤ f(y) + ⟨∇f(y), x⁺ − y⟩ + ‖x⁺ − y‖²/(2h)`, which is all the estimate-sequence step uses. There are no restarts, no
phases and no horizon; the method is anytime. The algorithm itself is not claimed as new; the contribution is its analysis on
the (L0, L1) class, see below.

## Guarantee

Write `L* = L0 + L1 G`. For every valid instance the point held after

    budget = 3 ⌈ 4 + 61 √(L* R²/ε)
                 + (35 + 1067 L1 R) · log(1 + (12 + 400 L1 R)(1 + 1/√(L* h0) + L1 √(Δ/L*)))
                 + 4 · log(5/2 + 1/(16 L* h0) + 22 L1² Δ/L*)
                 + 2 · log(2 (1 + h0 (40 L* + 400 L1² Δ)) (8 (1 + 32 L1 R)² + 200 L1² R²)) ⌉

oracle calls lies in `Q` and satisfies `F(x̂) − F(x*) ≤ ε` (`theorem result : Convergence spec budget`). In order notation,

    O( √((L0 + L1‖∇f(x*)‖) R²/ε) + (1 + L1 R) · log(2 + L1 R + 1/(L* h0) + L1²Δ/L* + L* h0 + L1²Δ h0) ).

The leading term is the one of the known-parameter composite theorem, with the constant `L0 + L1‖∇f(x*)‖` rather than
`L0 + L1 sup‖∇f‖`; the logarithm is ε-free; `h0` enters only through logarithms, so both very small and very large initial
steps are allowed; and every call of every rejected trial is counted. `G` may be taken as any upper bound on `‖∇f(x*)‖`;
for unconstrained problems with `ψ` Lipschitz one has `‖∇f(x*)‖ ≤ Lip(ψ)`, so the bound can also be read with that constant.
The lower-bound remark of [`CompositeGeneralizedAccelerated.md`](CompositeGeneralizedAccelerated.md) applies verbatim (same
instance class and oracles: `f = G x₁ + q(x₂, …)`, `ψ = G|x₁|` or a constraint fixing `x₁ = 0`, so that `‖∇f‖ ≥ G` everywhere,
`f` is (L0, L1)-smooth whenever `q` is `(L0 + L1 G)`-smooth, and the prox reveals nothing about `q`), so the leading term
`√((L0 + L1 G) R²/ε)` cannot be improved by any method with these oracles, up to constants. This lower-bound remark is
not formalized in Lean.

## What is new, and what is not

| source | problem | calls for `F − F* ≤ ε` (constants dropped) | supplied to the method |
|---|---|---|---|
| Nesterov's backtracking composite FGM ([2013](https://doi.org/10.1007/s10107-012-0629-5), Sec. 4), analysed under global smoothness `L` on `B(x*, cR)` | composite | `√(L_eff R²/ε)·log`, `L_eff ≤ (L0 + L1 G) exp(c L1 R)` on the ball (Gorbunov et al., Lemma 2.1) | `h0` |
| Gorbunov et al. ([ICLR 2025](https://arxiv.org/abs/2409.14989)), Vankov et al. ([ICLR 2025](https://arxiv.org/abs/2410.10800)), Tyurin ([ICML 2026](https://arxiv.org/abs/2508.06884)) | unconstrained | `√(L0R²/ε)` + start-up (exponential, `(L1R)^{2/3} log`, `L1R log`) | `L0, L1` (+ `R`, `Γ0`) |
| Borodich–Kovalev GRAAL ([ICLR 2026](https://arxiv.org/abs/2507.09823)), Cor. 3 | unconstrained | `√(L0D²/ε) + (L1D)³ + …` | `η0` |
| Richtárik, Gruntkowska, Li ([arXiv:2605.08850](https://arxiv.org/abs/2605.08850)), Prop. E.2 / Thm D.12 | constrained, unaccelerated | `(L0 + L1‖∇f(x*)‖) R²/ε`-type, criterion `min‖∇f(x_k) − ∇f(x*)‖` | `L0, L1, ‖∇f(x*)‖` |
| adaptive proximal gradient: Malitsky–Mishchenko AdProxGD ([arXiv:2308.02261](https://arxiv.org/abs/2308.02261)), Oikonomidis et al. ([arXiv:2402.06271](https://arxiv.org/abs/2402.06271)), Ou–Latafat–Themelis ([arXiv:2508.01353](https://arxiv.org/abs/2508.01353)) | composite, locally smooth or relatively smooth `f` | `O(1/k)` with local constants (not accelerated) | nothing |
| Li–Lan AC-FGM ([arXiv:2310.10082v3](https://arxiv.org/abs/2310.10082)), Cor. 1 | composite, parameter-free, no line search; step rule uses function values (Eq. 2.13) | `L̂_k R²/k²` with `L̂_k = max_t L_t` the largest local estimate; on this class only known to be `≤ (L0 + L1G) exp(c L1 R)` | nothing (function values) |
| adaptive accelerated methods: Suh–Ma AdaNAG ([arXiv:2505.11670](https://arxiv.org/abs/2505.11670)), Wang–Peypouquet ([arXiv:2512.20478](https://arxiv.org/abs/2512.20478)) | smooth convex, global `L` | `√(LR²/ε)` | nothing |
| this repository, [`CompositeGeneralizedAccelerated`](CompositeGeneralizedAccelerated.md) | composite | `√(L*R²/ε) + (1 + L1R)·log(2 + (3 + 96L1R)√(Δ/(L0R²)))` | `L0, L1, R, Δ` |
| this repository, [`BacktrackingGeneralizedAccelerated`](BacktrackingGeneralizedAccelerated.md) | unconstrained | `√(L0R²/ε) + (1 + L1R)·log(…)` | nothing |
| **this theorem** | composite | `√(L*R²/ε) + (1 + L1R)·log(ε-free)` | nothing (`h0 > 0` arbitrary) |

The leading term `√((L0 + L1‖∇f(x*)‖) R²/ε)` is **not** new: it is the repository's known-parameter composite bound and it is
optimal already for `L1 = 0`. Parameter-free accelerated methods for composite problems are also **not** new: AC-FGM of Li and
Lan is one (it is even line-search free). What is new is the *guarantee on the (L0, L1) class*: a bound with the polynomial
start-up `(1 + L1 R)·log` and the constant `L0 + L1‖∇f(x*)‖` in the leading term, obtained by a method that receives no problem
parameter, for composite or constrained problems where `∇f(x*) ≠ 0` and the self-bounding identity
`‖∇f(x)‖² ≲ (L0 + L1‖∇f(x)‖)(f(x) − f*)` of the unconstrained analyses is unavailable. The adaptive proximal-gradient methods are
unaccelerated, and the bounds of the adaptive accelerated methods carry the largest local smoothness estimate met along the run
(`L̂_k` for AC-FGM, Corollary 1 of [arXiv:2310.10082v3](https://arxiv.org/abs/2310.10082)); on this class that estimate is
only known to be at most `(L0 + L1 G)·exp(c L1 R)` on the ball `B(x*, cR)` (Gorbunov et al., Lemma 2.1). Whether the AC-FGM
trajectory keeps its local estimates polynomially bounded is not resolved here: its iterates are bounded (its Theorem 2.1), but
its analysis gives no bound on the gradient norms at the points where the estimates are taken, and a polynomial bound would
require a trajectory-level argument of the kind given below for the backtracking method. AC-FGM also uses function values,
which the gradient-plus-prox oracle model of this setup does not provide.

**Where the result is worse.** (i) It is not searchless: an accepted step costs three calls and every rejection three more;
the budget counts about six calls per accepted step. (ii) The logarithm is ε-free but not constant: `Δ` can be as large as
`(L0/L1²) exp(L1 R)`, so the start-up term can be of order `(L1 R)²` in the worst case (as for the known-parameter bounds).
(iii) With `L0, L1, R, Δ` known, the repository's composite method needs about half the calls. (iv) `h0` very far from
`1/L*` costs a logarithm. (v) Exact gradients and exact prox; deterministic.

## Mechanism

Write `M_x = L0 + L1‖∇f(x)‖`, `g* = ∇f(x*)`, `c = 1 + 32 L1 R`, and the potential `Φ = A(F(x) − F*) + ½‖z − x*‖²`.

1. *Accepted steps.* By convexity the test gives the descent inequality with constant `1/(2h)`, and `a² = h(A + a)` is the
   similar-triangles condition `2Ma² ≤ A + a` with `M = 1/(2h)`; the classical one-step estimate (the repository's `stm_step`)
   gives `Φ⁺ ≤ Φ`, hence `Φ ≤ R²`, `‖x − x*‖, ‖z − x*‖ ≤ 2R`, `F(x) − F* ≤ R²/A`. No locality is needed here.
2. *Acceptance certificate for `A > 0` (`accepts_of_small`).* If `h ≤ 1/(4M_x)` and `h ≤ A/(4c²)` the trial is accepted.
   Indeed `a ≤ h + √(hA) ≤ A/c`, so the relative step `a/(A + a)` is at most `1/c`; the shifted cocoercivity bound
   `‖∇f(x) − g*‖² ≤ 8(M_x + L1‖∇f(x) − g*‖)(f(x) − f* − ⟨g*, x − x*⟩)` of the composite theorem, the first-order optimality of
   `x*` on `Q` and the prox three-point inequality give `‖p − x*‖ ≤ 21R/2`, hence `y` and `x⁺` lie within `25R/(2c) ≤ 1/(2L1)`
   of `x`, where `∇f` is `2M_x`-Lipschitz; thus `⟨g⁺ − g, x⁺ − y⟩ ≤ 2M_x‖x⁺ − y‖² ≤ ‖x⁺ − y‖²/(2h)`. This is the step
   where backtracking analyses relative to the extrapolated point `y` fail on this class: `y` mixes `z`, at distance up to
   `2R` from `x*`, and the gradient there has no polynomial bound; the certificate is anchored at the main iterate `x`, whose
   gap `F(x) − F* ≤ R²/A` is controlled.
3. *Acceptance certificate for the first trial (`accepts_first`).* At `A = 0` the trial is a prox step from `x0`; the
   three-point inequality with comparison point `x0` and optimality at `x*` give `‖p − x0‖² ≤ h((‖∇f(x0)‖ + G)‖p − x0‖ + Δ)`,
   and cocoercivity bounds `‖∇f(x0)‖ ≤ G + 16L1Δ + 2√(2L*Δ)`; so every `h ≤ 1/(12 L* + 176 L1²Δ)` is accepted.
4. *The test discovers the cap.* With the curvature bound `M_x ≤ 2L* + 24L1²R²/A` along the run, every trial with
   `h ≤ gfun(A) := min(A/(8L*A + 96L1²R²), A/(4c²))` is accepted, so a rejection means `h > gfun(A)`. The threshold is
   proportional to `A` itself while `A ≲ L1²R²/L*`: this is the cap `a/A ≲ 1/(L1R)` that the known-parameter method imposes by
   hand, found here by the test without `R`. Because `gfun` is increasing and `gfun(2A) ≤ 2gfun(A)`, doubling after acceptance
   never falls behind: every accepted step satisfies `h ≥ min(2^{accepts}·A_min, gfun(A)/2)` with
   `A_min = min(h0, 1/(24L* + 352L1²Δ))` (the `a > A` case is handled by `a ≤ 2h`).
5. *Two growth regimes and counting.* `a ≥ √(hA)`, so `√A` grows by `√h/4` per accepted step (or `A` doubles if `h > A`);
   with `h ≥ gfun(A)/2` this is additive, `1/(4√(32L*))`, once `A ≳ L1²R²/L*`, and geometric, factor `1 + 1/(12 + 400L1R)`,
   before. The trial step equals `h0·2^{accepts − rejections}` and never drops below `min(1/(12L* + 176L1²Δ), gfun(A_min))/2`,
   so `trials ≤ 2·accepts + log₂(h0/h_low)`; each trial is three calls.

## Formal statement

`spec` has `Public = (E, x0, h0)`, `Params = Public + (L0, L1, R, Δ, G, ε)`; `Instance`, `Query`, the prox objective and the
`admissible` predicate are textually identical to [`CompositeGeneralizedSmooth`](../Setups/CompositeGeneralizedSmooth.lean).
`successful` asks for a minimizer `x*` of `F` on `Q` with the output in `Q` and `F(output) − F(x*) ≤ ε` almost surely; the
method is deterministic, so this is a sure statement. `Convergence spec budget` is proved with
`makeAlgorithm = backtrackingComposite`; the execution after `budget` calls equals the trial-level recursion `run` after
`budget/3` trials (`execute_backtracking`), whose accepted count is bounded below by the rejection count
(`rej_bound`), and whose accuracy follows from the potential (`run_accuracy`, `trials_sufficient`). The proof uses no axioms
beyond `propext`, `Classical.choice`, `Quot.sound`.
