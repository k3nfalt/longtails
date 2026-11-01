# Everest's radius-only rate without the radius: an R- and ε-oblivious accelerated method for convex (L0,L1)-smooth optimization

This note explains the contribution formalized in
[`RadiusFreeGeneralizedAccelerated.lean`](RadiusFreeGeneralizedAccelerated.lean)
(`OracleTemplate.RadiusFreeSherpa.result : Convergence spec budget`).

## Setup

The [setup](../Setups/RadiusOnlyGeneralizedSmoothConvex.lean) is the **radius-only class** `P_R` of
Rudomanov, Fomin, Gasnikov and Stonyakin, *Descending Everest with First-Order Oracles*
([arXiv:2610.21461v1](https://arxiv.org/abs/2610.21461), Section 2), with a weaker information model.

- `E` is a real Hilbert space of any dimension; `f : E → ℝ` is convex and differentiable, and its gradient is differentiable with
  `‖D∇f(x)‖ ≤ L0 + L1‖∇f(x)‖` for all `x` (`L0, L1 > 0`). For twice differentiable functions this is the symmetric
  `(L0, L1)`-smoothness of Everest Definition 2.1 and Lemma 2.2(b), i.e. the condition of Zhang, He, Sra and Jadbabaie
  ([ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS)) and Gorbunov et al. ([ICLR 2025](https://arxiv.org/abs/2409.14989), Assumption 1.3).
- Some minimizer `x*` satisfies `‖x0 − x*‖ ≤ R`. **No bound on the initial optimality gap** `f(x0) − f*` is assumed; by Everest
  Lemma A.2 it can be as large as `(L0/L1²)(e^{L1R} − 1 − L1R)`.
- The oracle returns `∇f(x)`; the cost is the number of gradient calls; success is `f(x̂) − f* ≤ ε` for the returned point.
- **Information.** `Public = (E, x0, L0, L1)`. The radius `R` and the accuracy `ε` are fields of `Params` only, so the Lean types
  guarantee that the method never uses them; they appear only in the call budget. Everest's method uses `L0, L1, R, ε`.

Write `A = L0R²/ε` and `q = L1R`.

## Algorithm

[`RadiusFreeSherpa.algorithm`](../Algorithms/RadiusFreeSherpa.lean) runs two phases and returns the current primal point.

**Phase 1 (R-free SHERPA).** State `(A, x, v)`, initially `(0, x0, x0)`. One iteration: query `∇f(x)` and `∇f(v)`; put
`d = x − v`, `z(t) = v + t d`, `φ(t) = ⟨∇f(z(t)), d⟩` (nondecreasing in `t` by convexity).
- If `φ(0) ≥ 0`, accept `y = v`. Else if `φ(1) ≤ ‖∇f(x)‖²/(16 L(x))`, accept `y = x`, where `L(y) = L0 + L1‖∇f(y)‖`.
- Otherwise bisect on the sign of `φ`: probe the midpoint `t` of the bracket `[t₋, t₊]` (initially `[0, 1]`); if `φ(t) < 0` set
  `t₋ = t`; else accept `y = z(t)` as soon as the **observable test** `t·φ(t) ≤ ‖∇f(z(t))‖²/(16 L(z(t)))` holds, and set `t₊ = t`
  otherwise.
- After acceptance, with `G = ‖∇f(y)‖` and Everest's `Φ(G) = (L0/L1²)[(1 + L1G/L0) log(1 + L1G/L0) − L1G/L0]`, take the positive
  root `a` of `a² = (A + a)/(7 L(y)) + a Φ(G)/G²` and set `A ← A + a`, `x ← y − ∇f(y)/(4L(y))`, `v ← v − a ∇f(y)`.
- **Exit rule.** At every queried point `z` (including probes), if `‖∇f(z)‖ ≤ L0/(4L1)` Phase 1 ends with `z`.

**Phase 2.** The repository's parameter-free backtracking accelerated method
([`BacktrackingAccelerated.lean`](../Algorithms/BacktrackingAccelerated.lean), Nesterov's similar-triangles scheme with a
gradient-only acceptance test `⟨∇f(y − h∇f(y)), ∇f(y)⟩ ≥ ‖∇f(y)‖²/2`, after which `h` is doubled, or halved on rejection)
started at the exit point with initial trial step `h = 1/L0`. It is anytime; its current point is the output.

Everest's SHERPA (their Algorithm 2) differs in three places, all of which use `R`: a bisection depth
`m = ⌈log2(128(1 + 128L1²R² + L1R)²)⌉` fixed in advance, an iteration cap `K = ⌈60 L1R⌉` (stated for `L1R ≥ 1`; otherwise they replace
`L1` by `1/R`), and the early-stop test `R‖∇f(z)‖ ≤ L0/(128L1²)` certifying a gap of at most `L0/(128L1²)` (their Lemma 3.3(a)); its
second stage CRUISE (Algorithm 3) uses `Γ0 = L0/(64L1²R²)` and `N = ⌈√(18L0R²/ε)⌉` and is run only when `ε < L0/(128L1²)`. The present
method needs no case distinction on `L1R`.

## Guarantee

For every valid instance, after

    budget = ⌈ 64 √(L0R²/ε) + 32768 (1 + L1R) log(2 + L1R) ⌉

gradient calls the returned point satisfies `f(x̂) − f* ≤ ε` (`theorem result`). In order notation,

    O( √(L0R²/ε) + (1 + L1R) · log(2 + L1R) ),

with every call counted: both calls opening an iteration, every bisection probe, and both calls of every Phase-2 trial
(accepted or rejected). The constants are not optimized.

## Contribution

The result is an **adaptivity** statement, not a complexity improvement: Everest's near-optimal radius-only complexity
`Θ̃(√A + L1R)` (their Theorem 3.7 upper bound `5√A + 240(1 + L1R)log2(64(1 + L1R)) + 2`, their Theorem 4.10 lower bound
`1 + N ≥ (1/29)[1 + √A + L1R/√log(2 + L1R)]` for deterministic first-order methods when `L0R² ≥ ε`) is attained by a method that receives only `L0, L1, x0` and is anytime in
`ε`. Against R-oblivious methods the gain is polynomial, `q² → q log q`:

| method | supplied to the method | calls in `P_R` (transient term) |
|---|---|---|
| Everest SHERPA + CRUISE, Thm 3.7 ([2610.21461v1](https://arxiv.org/abs/2610.21461)) | `L0, L1, R, ε` | `5√A + O((1 + q) log(2 + q))` |
| Tyurin, Thm 4.3 ([2508.06884v2](https://arxiv.org/abs/2508.06884), ICML 2026) | `L0, L1, R̄ ≥ R, Γ0 ≥ 2Δ/R²` | `√A + L1R̄ log(min{L1²R̄²Γ0/L0, Γ0R²/ε})`, i.e. `Θ(q²)` in `P_R` |
| repository `BacktrackingGeneralizedAccelerated` (parameter-free) | nothing | `√A + 26(1+q) log(… + 5L1²Δ/(4L0) + …)`, i.e. `Θ(q²)` in `P_R` (`Δ` up to `(L0/L1²)e^{q}`) |
| Vankov et al. AGMsDR, Thm 6.2 ([2410.10800v3](https://arxiv.org/abs/2410.10800), ICLR 2025) | `L0, L1` + exact one-dimensional minimization oracle | `√A + q^{2/3} log(F0/ε)` iterations, i.e. `Θ(q^{5/3})` in `P_R`, not gradient-only |
| Gorbunov et al. (L0,L1)-GD ([2409.14989](https://arxiv.org/abs/2409.14989), ICLR 2025) | `L0, L1` | `A + q²` (not accelerated) |
| Borodich–Kovalev aGRAAL ([ICLR 2026](https://arxiv.org/abs/2507.09823), Cor. 3) | initial step | `√A + (L1D)³` |
| DADA ([2501.10258v2](https://arxiv.org/abs/2501.10258), ICLR 2026, Cor. D.20) | radius guess `r̄` | `(L0R²/ε + L1²R²) log²` (not accelerated) |
| El Bakkali El Kadi–Gorbunov, Thm 2 / Rem. 2 ([2610.23301v2](https://arxiv.org/abs/2610.23301), Oct 2026, stochastic HP; σ = 0 case) | `L0, L1, R0, Δ̄0, δ` | `√A + Õ((1 + q)²)` (one-phase; two-phase Thm 1 also `(L1R0)²`) |
| Okazaki–Yagishita–Hino NGM-RA ([2610.27681v1](https://arxiv.org/abs/2610.27681), Oct 2026) | nothing (parameter-free) | `Õ((L0/ε + L1²) R²)` (not accelerated) |
| **this theorem** | `L0, L1` | `√A + (1 + q) log(2 + q)` |

Thus, as of 31 October 2026 (arXiv re-checked on that date; Everest has a single version v1 of 15 October 2026 and no follow-up),
every gradient-only method whose updates do not use `R` paid a transient of order `q²` in `P_R`
(the repository's own parameter-free theorem, Tyurin's method with the trivial `R̄`, Gorbunov et al., NGM-RA; the October 2026
stochastic accelerated methods of El Bakkali El Kadi–Gorbunov also pay `(1 + L1R0)²` and take `R0` as input), and the only sub-`q²`
R-oblivious method (AGMsDR) needs an exact line-minimization oracle and still pays `q^{5/3}`. The lower bound
`Ω(√A + q/√log(2 + q))` holds for all deterministic first-order methods, so the new bound is optimal up to logarithms also within
the smaller information model.

**Regime of the gain.** The transient dominates when `(1 + q) log(2 + q) ≳ √A`, i.e. for moderate accuracy or large `L1R`; for
`√A ≫ q log q` all accelerated methods are comparable.

### Technical mechanism

1. *Observable acceptance.* Everest's Lemma 3.3 guarantees, after a depth `m(R)` bisection, a point `y` on `[v, x]` with
   `f(y) ≤ f(x)` and `⟨∇f(y), y − v⟩ ≤ ‖∇f(y)‖²/(16L(y))`. The first condition is not observable, but `φ(t) ≥ 0` implies it by convexity
   (`f(x) ≥ f(z(t)) + (1 − t)φ(t)`); the second is observable. Accepting at the first probe satisfying both removes `R` from the
   search. The potential `A_k(f(x_k) − f*) + ½Σ a_i²‖∇f(y_i)‖² + ½‖v_k − x*‖² ≤ R²/2` (Everest Lemma 3.4, with the Φ-inequality
   `f(y) + ⟨∇f(y), x* − y⟩ + Φ(‖∇f(y)‖) ≤ f*`) is unchanged.
2. *Probe count without R.* While no probe is accepted, the bracket endpoints satisfy `φ(t₋) < 0` and
   `t₊φ(t₊) > ‖∇f(z₊)‖²/(16L(z₊))`; the argument of Everest's Appendix A.5 (proof of their Lemma 3.3), run with the
local Lipschitz bound `‖∇f(z) − ∇f(z')‖ ≤ 2L(z')‖z − z'‖` for `L1‖z − z'‖ ≤ 1/2`, then forces the bracket width above
`1/(800 (L1‖x − v‖)²)` as long as
   every probe has `‖∇f‖ > L0/(4L1)`. Hence at most `⌈log2(3200(1 + q)²)⌉` probes per iteration, using only that all points lie in
   `B(x*, R)` — a fact of the analysis, not of the algorithm.
3. *Exit certificate.* Everest certify `gap ≤ L0/(128L1²)` through `R‖∇f(z)‖ ≤ L0/(128L1²)`; a gap certificate fundamentally needs the
   radius (`gap ≤ ⟨∇f(z), z − x*⟩ ≤ ‖∇f(z)‖‖z − x*‖`). We instead stop Phase 1 at the first point with `‖∇f‖ ≤ L0/(4L1)` and prove,
   by the descent lemma `gap(x) ≥ (5/24)‖∇f(x)‖²/L(x)`, that before the exit `gap(x_k) > L0/(96L1²)`, so Everest's counting
   (Lemma 3.5) still bounds the number of iterations by `O(1 + q)`. The exit point has gap at most `L0R/(4L1)`, which is not small,
   but the repository's parameter-free second stage tolerates it: its transient is `(1 + q) log(… + 5L1²Δ'/(4L0) + …)` with
   `L1²Δ'/L0 = q/4`, hence `O((1 + q) log(2 + q))`, instead of `q²` when started at `x0`.
4. *Counting.* The iteration count is proved by an incremental potential: each accepted iteration increases
   `(L1a‖∇f‖)²/(1+q) + 2√14·√(L0A) + 14√(1+q)·log⁺(A/A_min)` by at least one (or crosses the level `A_min = e^{−√(1+q)−1}/(7L0)`
   once), using Everest's identity `L1 a_k G_k = L1Φ(G_k)/G_k + (A_k/(7a_k))·L1G_k/L(y_k)`; the three terms are bounded by `R²`,
   `48q²` and `O(√(1+q) log(1+q))`.

### What is not claimed

- No improvement of Everest's complexity; the logarithm from the bisection remains, and the line search is not removed (Everest's
  open question). The method is R- and ε-oblivious but **not parameter-free**: `L0, L1` are supplied, as in Tyurin, Vankov et al.
  and Gorbunov et al.
- `L1 = 0` and `R = 0` are excluded (`valid` requires `L0, L1, R, ε > 0`); `L1 = 0` is the classical smooth class.
- Constants are loose (universal factors only); no lower bound is proved here.

## Nonlinear instances

Convex functions with Hessian growing with the gradient: `‖Bx − y‖_p^p` with `p > 2` and univariate polynomials of degree at least
three (Zhang et al. 2020, Everest Section 1), penalized duals of distributionally robust problems (Everest Section 1), conjugates of
strongly convex functions on polytopes (Everest Section 4, Lemmas 4.2 and 4.4), and sums of exponentials such as Poisson regression
`Σ_j exp((Bx)_j) − y_j(Bx)_j` in the regime treated by Gorbunov et al. (§1). For these families finite `(L0, L1)` are determined by the
data, whereas `R` depends on the unknown minimizer; started far from it, the initial gradient and gap are exponential in `L1R`
(Everest Lemma A.2), which is exactly the regime where Phase 1 matters.

## Formal proof map

[`RadiusFreeSherpaBasic`](../Proofs/RadiusFreeSherpaBasic.lean): segment form of smoothness from the Hessian form, Φ and the Φ-inequality,
weight rule, descent lemma. [`RadiusFreeSherpaStep`](../Proofs/RadiusFreeSherpaStep.lean): one accepted iteration decreases the potential.
[`RadiusFreeSherpaSearch`](../Proofs/RadiusFreeSherpaSearch.lean): bisection invariant and width bound. [`RadiusFreeSherpaCount`](../Proofs/RadiusFreeSherpaCount.lean):
incremental iteration count. [`RadiusFreeSherpaRun`](../Proofs/RadiusFreeSherpaRun.lean): state-machine invariant, termination of Phase 1,
hand-off and output identification. [`RadiusFreeSherpaBudget`](../Proofs/RadiusFreeSherpaBudget.lean): budget arithmetic. Phase 2 reuses
`ParameterFreeGeneralized.trial_accuracy` and `budget_bound` from the repository's parameter-free theorem, instantiated at the exit point.
