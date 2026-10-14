# Accelerated zeroth-order optimization under matrix (L0, L1)-smoothness with effective-dimension complexity

This note explains the result formalized as
[`OracleTemplate.MatrixGeneralizedZO.result`](ZerothOrderMatrixGeneralizedAccelerated.lean), with the
[setup](../Setups/ZerothOrderMatrixGeneralizedSmooth.lean) and the
[algorithm](../Algorithms/MatrixGeneralizedZO.lean).

In one sentence: for convex functions whose curvature is bounded by a generalized-smoothness factor
`L0 + L1·N(∇f(x))` times an unknown matrix `H` of trace `r`, a zeroth-order method that sees only exact
function values finds an `ε`-minimizer with probability `1 − δ` using

    O( log(1/δ) · [ √(d(r+1)) · √(L0 R²/ε) + (r + 1 + L1 R √(d(r+1))) · log(e + Δ/ε) ] )

function evaluations. With `r ≪ d`, the leading term is `√(d/r)` times smaller than for finite differences
combined with the best accelerated first-order method for `(L0, L1)`-smooth functions, for every `ε`. The
repetition factor `log(1/δ)` is the only exception. The `L1 R` part of the start-up also improves by `√(d/r)`,
but only up to the ratio of two logarithms; see the regimes below. The `L1 = 0` special case recovers the known
`√(d·tr H)`-type accelerated rate.

## Setup

The [setup](../Setups/ZerothOrderMatrixGeneralizedSmooth.lean) fixes `x ∈ ℝ^d` (Euclidean) and public parameters
`d ≥ 1`, `L0 > 0`, `L1 ≥ 0`, `r > 0`, `R > 0`, `Δ > 0`, `ε > 0`, `0 < δ < 1` and `x0`.

- **Objective.** `f` is convex and differentiable with a differentiable gradient. Some minimizer `x*` satisfies
  `‖x0 − x*‖ ≤ R` and `f(x0) − f(x*) ≤ Δ`.
- **Curvature geometry (unknown).** There is a self-adjoint linear map `H` with `μ_H I ≼ H ≼ I` for some
  `μ_H > 0` and `tr H = Σ_i ⟨H e_i, e_i⟩ ≤ r`. Write `‖v‖_H = √⟨Hv, v⟩` and let
  `N(g) = sup{⟨g, w⟩ : ‖w‖_H ≤ 1}` be the dual norm, so `‖g‖ ≤ N(g)`.
- **Matrix generalized smoothness.** For every `x`, every `c ≥ N(∇f(x))` and all `v, w`,
  `⟨∇²f(x) v, w⟩ ≤ (L0 + L1 c) ‖v‖_H ‖w‖_H`. For convex `C²` functions this is exactly
  `∇²f(x) ≼ (L0 + L1 N(∇f(x))) H`. In Lean the condition is stated with "certificates" `c` (any `c` with
  `⟨∇f(x), w⟩ ≤ c ‖w‖_H` for all `w`), which avoids pseudo-inverses.
- **Oracle.** Every query `x` returns the exact value `f(x)` (any oracle whose answers equal `f`).
- **Information.** The algorithm is built from the public parameters only. `H`, `μ_H`, `x*` and `f` are not
  available to it; `r` (an upper bound on `tr H`) is public.
- **Success.** The returned point `x̂` satisfies `P[f(x̂) − f(x*) > ε] ≤ δ` over the algorithm's random signs.

Provenance and scope of the assumptions:

- `H = I` gives exactly the Hessian `(L0, L1)`-condition `‖∇²f(x)‖ ≤ L0 + L1‖∇f(x)‖` of
  [Zhang, He, Sra, Jadbabaie (ICLR 2020)](https://openreview.net/forum?id=BJgnXpVYwS) with `r = d`.
- `L1 = 0` is the matrix (effective-rank) smoothness `∇²f ≼ L0 H` used for zeroth-order methods by
  [Malladi et al. (NeurIPS 2023), local effective rank](https://arxiv.org/abs/2305.17333),
  [Yue, Yang, Fang, Lin (COLT 2023)](https://proceedings.mlr.press/v195/yue23b.html), and, for diagonal `H`,
  coordinate smoothness `Σ_i L_i` in [Nesterov (SIOPT 2012)](https://doi.org/10.1137/100802001).
- The combination of `(L0, L1)` with an `H`-norm appears in one unreviewed preprint,
  [Ye and Luo, arXiv:2602.01627](https://arxiv.org/abs/2602.01627) (Assumption 1, nonconvex), with the
  Euclidean gradient norm in the `L1` term. Our dual-norm version is weaker for the same `H` because
  `N(g) ≥ ‖g‖`. This combination is therefore a new, mildly generalized assumption supported by one preprint.
- `μ_H > 0` excludes exactly singular `H`. This costs little: `H + μI` has trace `r + dμ`. It also excludes the
  exact-low-rank case, which would otherwise be solved faster by first identifying the subspace.

**Instance family.** Let `f(x) = Σ_j (exp((Ax)_j) − y_j (Ax)_j)` with `A ∈ ℝ^{d×d}` invertible, `‖A‖ = 1`, and
`y_j > 0` (a Poisson-type generalized linear model). Then `∇²f = Aᵀ diag(e^{Ax}) A`, and with `H = AᵀA`:

- `N(∇f(x)) = ‖e^{Ax} − y‖`;
- `diag(e^{Ax}) ≼ (max_j y_j + ‖e^{Ax} − y‖) I`, so the condition holds with `(L0, L1) = (max_j y_j, 1)`;
- `r = Σ_i σ_i(A)²`.

For power-law spectra `σ_i = i^{−α}` with `α > 1/2`, `r = O(1)` (or `O(log d)` at `α = 1/2`), while `rank H = d`.
The coordinates interact, the minimizer `A^{-1} log y` exists, and `f` is not globally `L`-smooth.

## Algorithm

[`algorithm`](../Algorithms/MatrixGeneralizedZO.lean) runs `N = ⌈log₂(1/δ)⌉` independent copies of the
following method and returns the run output with the smallest function value.

The constants are `rp = 48r + 16`, `L1' = max(L1, 1/(R√d))`, `θcap = min(1/4, 2/(r+2))` and
`F(A) = 8R²/A`. From these, define
`Gb(F) = 4 L1' F + 2√(L0 F)`, `Mb(F) = L0 + L1' Gb(F)`, `s(A) = 1/(8 Mb(F(A)) rp)`,
`a(A) = min(√(A s(A)/(8d)), θcap A)` and `λ(A) = 1/(2 L1' s(A) √(48 r))`.

The weights follow a **deterministic schedule** `A_0 = R²/(2Δ)`, `A_{k+1} = A_k + a(A_k)`; the method does not
adapt its schedule to observed values. Start from `x_0 = z_0 = x0`. Iteration `k` uses four function evaluations:

    y_k   = (A_k x_k + a_k z_k)/(A_k + a_k),          u_k uniform in {±1}^d
    D̂_k   = (f(y_k + h_k u_k) − f(y_k − h_k u_k)) / (2 h_k)            (2 evaluations)
    x̃     = y_k − s_k · clip_{λ_k}(D̂_k) · u_k
    x_{k+1} = x̃ if f(x̃) ≤ f(y_k), else y_k                             (2 evaluations)
    z_{k+1} = z_k − a_k D̂_k u_k

The finite-difference step `h_k` is an explicit function of public quantities (`fdStep`). The run stops after
`K` iterations and evaluates `f(x_K)` once for the final selection. There are no restarts, no line searches,
no gradient-norm estimates and no knowledge of `H`.

## Proved guarantee

With

    K = ⌈510 √(d(r+1) L0 R²/ε) + 1300 (r + 1 + L1 R √(d(r+1))) · log(e + 8Δ/ε)⌉

the public budget is the one-line formula

    budget = ⌈log₂(1/δ)⌉ · (4K + 1).

It counts the four evaluations per iteration and the final evaluation of each run, which is used for selection.
The theorem states `P[f(x̂) − f(x*) > ε] ≤ δ`. All constants are explicit, and no `O(·)` is hidden in the Lean
statement.

## Mechanism and what is new

The `L1 = 0` rate is not new: accelerated coordinate and random-direction methods under matrix smoothness give
`√(d · tr H)`-type complexity
([Nesterov and Stich, SIOPT 2017](https://doi.org/10.1137/16M1060182);
[Allen-Zhu, Qu, Richtárik, Yuan, ICML 2016](https://proceedings.mlr.press/v48/allen-zhuc16.html)).

A concurrent, unreviewed ICLR 2027 submission,
[Randomized Subspace Nesterov Accelerated Gradient (OpenReview EcZ8v3vs2g)](https://openreview.net/forum?id=EcZ8v3vs2g),
also studies `L1 = 0` randomized-subspace acceleration under matrix smoothness.

What is new is an accelerated randomized-direction method under generalized smoothness. The obstruction is real.
Accelerated `(L0, L1)` methods choose their weights from the local constant `L0 + L1 N(∇f(y_k))`. A single
direction does not reveal `N(∇f(y_k))`, `H` is unknown, and the momentum points can enter regions of exponential
curvature. The proof replaces observed curvature with a *certified* curvature bound and proves that the momentum
point stays inside the certified region.

1. **Certified gradient bound.** On the event `Ψ_k ≤ 4R²` (below),
   - the potential gives `f(x_k) − f* ≤ 4R²/A_k`;
   - an `H`-local Taylor argument along `[x_k, z_k]` gives `f(y_k) − f* ≤ F(A_k)`;
   - `(L0, L1)`-cocoercivity in the dual norm gives `N(∇f) ≤ Gb(f − f*)`
     ([`dnorm_sq_le`](../Proofs/MatrixGeneralizedLocal.lean)).

   So `L0 + L1 N(∇f(y_k)) ≤ Mb(F(A_k))`, which is exactly what the schedule uses
   ([`locality`](../Proofs/MatrixGeneralizedStepLocal.lean)).
2. **H-locality of the momentum point.** The certificate needs `‖z_k − x_k‖_H ≲ √(d·rp)·R`.
   - Write `x_k = p_k + e_k`, where `p_k` is a convex combination of `x0` and the `z_j`, and the lag
     `e_{k+1} = e_k/(1+θ_k) − (step)` collects the random steps.
   - The lag is controlled inside the single potential
     `Ψ_k = A_k (f(x_k) − f*) + ‖z_k − x*‖²/2 + γ_k ‖e_k‖_H²`, with `γ_k = a_k/(64 s_k)`.
   - The proof shows `γ_{k+1} ≤ (1+θ_k) γ_k` and that the `H`-norm variance `s_k² E[c² uᵀHu] ≤ O(r s_k² G²)` is
     absorbed by the dissipation of `Φ`.
3. **Variance with `r` instead of `d`.**
   - Rademacher moments give `E[⟨g,u⟩² uᵀHu] ≤ ‖g‖²(tr H + 2)`
     ([`expect_inner_sq_quad`](../Proofs/MatrixGeneralizedRademacher.lean)).
   - The clipped step stays inside the trust region on the event `uᵀHu ≤ 48r`, which Markov's inequality makes
     likely. Outside it, the function-value safeguard prevents any increase. This gives `rp = O(r)`, not
     `r + √d` ([`xstep_expect`](../Proofs/MatrixGeneralizedStep.lean)).
4. **Probability.**
   - `E[Ψ_{k+1}] ≤ Ψ_k + 9R²/(32·2^k)` while `Ψ_k ≤ 4R²` ([`main_step`](../Proofs/MatrixGeneralizedStep.lean)).
     The error term comes from the finite differences.
   - A Ville-type induction on the finite tree of signs gives failure probability at most `1/2` per run (the proof shows `25/64`)
     ([`run_fail_prob`](../Proofs/MatrixGeneralizedRun.lean)).
   - Independent runs and exact-value selection give `δ`.
5. **Growth.** The deterministic schedule grows geometrically while `L1` dominates and quadratically afterwards
   (a potential-counting argument, [`sched_iterations`](../Proofs/MatrixGeneralizedSchedule.lean)), so
   `A_K ≥ 4R²/ε`.

The strongest rejection argument is that this is an incremental port of accelerated coordinate descent. The
answer is that neither ingredient transfers on its own. The `L1 = 0` analyses need a global curvature bound,
which under `(L0, L1)` is `L0 e^{O(L1 R)}` on the relevant ball. First-order `(L0, L1)` acceleration observes
`‖∇f‖` at the query point. Here locality must be certified from the potential alone and proved for momentum
points of a randomized method; items 1 and 2 above are the new part.

## Comparison with the closest results (total function evaluations, constants omitted)

| method | leading term (ε → 0) | `L1` start-up | notes |
|---|---|---|---|
| **this result** | `√(d r) √(L0 R²/ε)` | `(r + L1 R √(d r)) log(e + Δ/ε)` | times `log(1/δ)`; exact values |
| finite differences + [Tyurin (ICML 2026), Thm 4.3](https://arxiv.org/abs/2508.06884) | `d √(L0 R²/ε)` | `d L1 R log(min{L1²Δ/L0, Δ/ε})` | deterministic; strongest first-order baseline |
| finite differences + AGMsDR ([Vankov et al., ICLR 2025](https://arxiv.org/abs/2410.10800)) / [repo GeneralizedAcceleratedConvex](GeneralizedAcceleratedConvex.lean) | `d √(L0 R²/ε)` | `d (L1 R)^{2/3} log(·)` | |
| finite differences + (L0,L1)-GD ([Vankov et al., ICLR 2025](https://arxiv.org/abs/2410.10800)) | `d L0 R²/ε` | `d L1 R log(Δ/ε)` | |
| finite differences + clipped GD ([Gorbunov et al., ICLR 2025](https://arxiv.org/abs/2409.14989)) | `d L0 R²/ε` | `d L1² R²` | |
| random coordinates + line search ([Lobanov et al., arXiv:2412.17050](https://arxiv.org/abs/2412.17050), Thm 4.3) | `d L0 R²/ε` | `d L1 R log(·)` | coordinate-wise `(L0,L1)`; not accelerated |
| [Lobanov and Gasnikov, arXiv:2501.18198](https://arxiv.org/abs/2501.18198), Thms 5.2/5.4 | `O~(d σ² M R⁴/ε³)` | — | noisy two-point; assumes a trajectory gradient bound `M` |
| `L1 = 0` accelerated coordinate/sketch methods | `√(d tr H) √(L R²/ε)` | — | need a global `L`; under `(L0,L1)` this is `L0 e^{O(L1 R)}` |

Regimes (assuming `r ≥ 1`; otherwise read `r + 1` for `r`):

- **Leading term.** It improves on every finite-difference baseline by `√(d/r)` for all `ε`, provided
  `log(1/δ) ≲ √(d/r)`.
- **`L1` start-up against Tyurin.** Write `ℓ_T = log(min{L1²Δ/L0, Δ/ε})` for Tyurin's logarithm and
  `ℓ = log(e + 8Δ/ε)` for ours. Then

      L1 R √(d r) · ℓ  ≤  √(r/d) · (ℓ/ℓ_T) · d L1 R · ℓ_T,

  so the improvement is `√(d/r)` up to the ratio `ℓ/ℓ_T`. The ratio is `O(1)` when `ε ≳ L0/L1²`. For smaller
  `ε`, Tyurin's start-up stops growing with `1/ε`, while ours keeps the factor `log(e + 8Δ/ε)`; the ratio is
  then at most `log(e + 8Δ/ε)/log(L1²Δ/L0)`.
- **Additive start-up term.** `(r + 1) log(e + Δ/ε)` has no counterpart in the first-order baseline. It
  dominates the `L1` part only when `L1 R ≲ √(r/d)`, and it is always of lower order than the leading term as
  `ε → 0`.
- **`L1` start-up against AGMsDR.** Against the `(L1R)^{2/3}` start-up, the `L1` part is better only when
  `(L1R)^{1/3} ≲ √(d/r)`, again up to logarithms.

These comparisons are against the finite-difference reduction class. No lower bound in `r` is claimed.

## Other comparisons and non-collapse

- **Two-phase composition.** Running an unaccelerated method until gradients are small, then an `L1 = 0`
  accelerated method, fails because momentum points leave every certified region. The only global constant on
  the `R`-ball is `L0 e^{O(L1 R)}`.
- **Localization.** Ball or proximal localization (Monteiro–Svaiter, ball oracles) on radius `1/L1` adds a
  full-rank regularizer `μI`. The inner Hessian bound becomes `M H + μ I`, with trace `M r + μ d`, which destroys
  the `tr H` dependence. An `H`-prox would need `H`, which is unknown.
- **Subspace identification.** This beats the method only when `rank H ≪ d`. It is excluded here by
  `μ_H > 0`, and it is irrelevant for full-rank decaying spectra.

## Limitations

- Exact function values only; noisy values are not covered.
- The success probability is boosted by `⌈log₂(1/δ)⌉` independent runs. The guarantee is in high probability,
  not in expectation, and the factor `log(1/δ)` multiplies the whole budget.
- The constants are large (`rp = 48 r + 16`, and the factors 510 and 1300). They come from conservative choices
  in the proof, not from tuning.
- `r` (an upper bound on `tr H`) and `L0`, `L1`, `R`, `Δ` must be known. The `L1` start-up is logarithmic in
  `Δ/ε` but carries `√(d r)`.
- The setup requires `μ_H > 0`, which rules out exactly singular `H`.
- The combined assumption has limited provenance (one unreviewed preprint, generalized here). Its natural
  instances are generalized linear models with decaying data spectra.

## Lean layout

- [Setup](../Setups/ZerothOrderMatrixGeneralizedSmooth.lean) and [algorithm](../Algorithms/MatrixGeneralizedZO.lean).
- [MatrixGeneralizedLocal](../Proofs/MatrixGeneralizedLocal.lean): the `H`-norm and dual norm, segment
  bootstrapping, the local descent lemma and cocoercivity.
- [MatrixGeneralizedRademacher](../Proofs/MatrixGeneralizedRademacher.lean): second and fourth sign moments and
  quadratic forms.
- [MatrixGeneralizedSchedule](../Proofs/MatrixGeneralizedSchedule.lean): the schedule, weight ratio, lag-weight
  lower bound and growth.
- [MatrixGeneralizedExpect](../Proofs/MatrixGeneralizedExpect.lean): finite Cauchy–Schwarz and Markov inequalities.
- [MatrixGeneralizedStepLocal](../Proofs/MatrixGeneralizedStepLocal.lean) and
  [MatrixGeneralizedStep](../Proofs/MatrixGeneralizedStep.lean): finite-difference error, the locality
  certificate, the safeguarded step, the dual and lag recursions, and the one-step supermartingale bound.
- [MatrixGeneralizedRun](../Proofs/MatrixGeneralizedRun.lean): trajectories, the Ville-type induction and the
  per-run failure probability.
- [MatrixGeneralizedExecution](../Proofs/MatrixGeneralizedExecution.lean): plan evaluation, best-of-runs
  selection, independence and measure conversion.
