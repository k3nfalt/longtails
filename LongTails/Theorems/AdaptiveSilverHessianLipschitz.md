# Long-step gradient descent beats `ε⁻²` on nonconvex functions with Lipschitz Hessians

Lean theorem: [`AdaptiveSilverHessianLipschitz.lean`](AdaptiveSilverHessianLipschitz.lean)
(`OracleTemplate.AdaptiveSilverHessianLipschitz.result`).
Setup: [`SmoothHessianLipschitzGd.lean`](../Setups/SmoothHessianLipschitzGd.lean).
Algorithm: [`AdaptiveSilverGd.lean`](../Algorithms/AdaptiveSilverGd.lean).

## Problem class, oracle, and accuracy

- **Objective.** `f : E → ℝ` on a finite-dimensional real inner-product space `E` of arbitrary dimension. No bound
  depends on `dim E`. The assumptions are:
  - `f` is `C²`;
  - `‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖`;
  - `‖∇²f(x) − ∇²f(y)‖ ≤ ρ‖x − y‖` in operator norm, where `∇²f = fderiv (gradient f)`;
  - `f(x₀) − f(x) ≤ Δ` for all `x`.

  These are the standard second-order-smooth nonconvex assumptions of
  [Carmon–Duchi–Hinder–Sidford](https://arxiv.org/abs/1611.00756) and
  [Li–Lin (JMLR 2023)](https://arxiv.org/abs/2201.11411). Nothing is added. In particular there is no weak-convexity
  bound, so strict saddles with `λ_min(∇²f) = −L` are allowed. `ρ ≥ 0` may be `0`. Because `f` is bounded
  below, a quadratic in this class is convex, so `ρ = 0` reduces to convex quadratics.
- **Oracle.** Exact gradients only. No function values and no Hessians.
- **Accuracy.** The output `x̂` satisfies `‖∇f(x̂)‖ ≤ ε`. The algorithm is deterministic, so this holds for every
  run. Lean states it almost surely with respect to the trivial seed law.
- **Admissible algorithms (`adaptiveGdFamily`).** Every query is the previous query minus `h · ∇f(previous query)`,
  with a step `h > 0` that may depend on the history (the algorithm state and the current gradient). The output is a
  queried point with the smallest observed gradient norm. There is no momentum and no extrapolation: every step is
  along the current negative gradient. The theorem proves that the constructed algorithm belongs to this family.

## Algorithm: gradient-norm-gated silver gradient descent

The algorithm uses the silver block of level `K` from
[Altschuler–Parrilo](https://arxiv.org/abs/2309.07879) (`SilverSchedule.steps K`, `ϱ = 1 + √2`). It has
`n = 2^K − 1` steps, scaled by `1/L`, with total step length `σ/L` where `σ = ϱ^K − 1`. The thresholds are
`G = ε·max(1, √(σ/(25n)))` and `M·G` with `M = √(4n+2)`.

- **Probe.** If `‖∇f(x)‖ > G`, take the step `x ← x − ∇f(x)/L`. Otherwise start a *cycle* at the current point.
- **Cycle.** A cycle is two consecutive silver blocks `[A, A]`, i.e. `2n` steps with sizes `h_{i mod n}/L`. Before
  each cycle step:
  - if the current gradient has norm `> M·G`, the cycle is **aborted**: take the step `1/L` and return to probing;
  - otherwise take the scheduled step.

  After `2n` steps, return to probing.
- **Level.** `K` is the largest `k ≥ 2` with `256 ρ² ε² ϱ^{9k} ≤ L⁴`, i.e. `16ρε(ϱ^k)^{9/2} ≤ L²`. It is capped
  at the least `k` with `ϱ^k ≥ 50LΔ/ε²`. If even `k = 2` fails, the method sets `G = ε`.
- **When the method is plain gradient descent.** Whenever `G = ε` (including the fallback just described, and small
  levels with `σ ≤ 25n`), a cycle can only start at a point that already satisfies `‖∇f‖ ≤ ε`. The method is then
  plain gradient descent with step `1/L`, and the accounting still holds.
- **Parameters used.** The method uses `L`, `ρ`, `ε` and `Δ`. It is adaptive (gradient-norm gated), *not* a
  predetermined step-size schedule.

## Guarantee

The Lean theorem proves `‖∇f(x̂)‖ ≤ ε` after

```
⌈90 · L · Δ · (ρε/L²)^(1/22) / ε²⌉ + ⌈400 · (LΔ/ε²)^(4/5)⌉ + 8
```

gradient evaluations. Every evaluation is counted, including those in aborted cycles. In rate form:

```
O( Δ L^{10/11} ρ^{1/22} ε^{−21/11}  +  (LΔ/ε²)^{4/5} ).
```

- **Exponent.** The proof establishes the exponent `a = 2(1 − log_ϱ 2)/9 ≈ 0.0475` in the factor
  `(ρε/L²)^a`. The public budget states the slightly weaker rational exponent `1/22 ≈ 0.0455`.
- **Second term.** It comes from one cycle length, `2^{K+1} ≤ O((LΔ/ε²)^{log_ϱ 2})`. It is the term that remains
  when `ρ → 0`. For `ρ = 0` (which reduces to convex quadratics) the bound is the convex long-step rate
  `O((LΔ/ε²)^{4/5})`.

## What is new

**Question answered.** Altschuler and Parrilo ([arXiv:2309.07879](https://arxiv.org/abs/2309.07879), §6
"Beyond convexity") ask whether stepsize hedging can give accelerated rates to `ε`-stationary points in nonconvex
optimization. [Grimmer–Shu–Wang (2309.09961)](https://arxiv.org/abs/2309.09961) also leave nonconvex long steps
open.

**What was known for GD on this class.**
- Exact worst-case analyses of GD on nonconvex `L`-smooth functions give `Θ(LΔ/N)` and cover only non-long
  constant or prescribed steps:
  - [Abbaszadehpeivasti–de Klerk–Zamani, 2104.05468](https://arxiv.org/abs/2104.05468);
  - [Rotaru–Glineur–Patrinos, 2406.17506](https://arxiv.org/abs/2406.17506), "Exact worst-case convergence rates
    of gradient descent: a complete analysis for all constant stepsizes over nonconvex and convex functions",
    which also covers hypoconvex functions.
- [Cartis–Gould–Toint (2010)](https://doi.org/10.1137/090774100) show `ε⁻²` for steepest descent under standard
  step rules. Long-step schedules are not covered.
- In this repository, [`WeaklyConvexSilver`](WeaklyConvexSilver.md) (unpublished, PR #63) obtains a polynomial
  gain only for `ρ_w`-weakly convex functions with `ρ_w ≪ L`. A Lipschitz Hessian gives only `L`-weak convexity,
  for which that bound yields no gain. Its certificate also needs weak-convexity inequalities between all iterates
  of a block, which fail as soon as a negative-curvature direction grows.

**This result.** To our knowledge (literature search through 2026-10-29), this is the first `o(ε⁻²)` guarantee for
momentum-free gradient descent on the standard class of nonconvex functions with Lipschitz gradient and Lipschitz
Hessian. The schedule must be adaptive only through gradient-norm tests.

**Comparison with the class optimum (no improvement for the class).**
- Momentum-based methods reach `O(Δ L^{1/2} ρ^{1/4} ε^{−7/4})`: CDHS17; restarted AGD, Li–Lin JMLR 2023.
- The classical published lower bound for this class is `Ω(ε^{−12/7})`
  ([Carmon–Duchi–Hinder–Sidford, Lower bounds II, Math. Program. 2021](https://arxiv.org/abs/1711.00841)).
- A matching `Ω(ε^{−7/4})` first-order lower bound is claimed by the unreviewed preprint
  [Zhou, arXiv:2606.05438v2](https://arxiv.org/abs/2606.05438).
- Our exponent gain `≈ 0.0475` is far from the `1/4` gain of momentum methods.
- No lower bound for gradient descent itself is proved, so the optimal exponent for GD is open. The heuristic
  ceiling of this mechanism (block length limited by the cubic Taylor error) is `≈ 0.107`. A finer bookkeeping that
  pays for aborts by the concave decrease would give `≈ 0.0535`.

## Technical mechanism

1. **Junction certificate.** Take two consecutive silver blocks `[A, A]` and the gradient at their junction `x_n`.
   Split the Taylor model at the cycle start into the nonnegative and negative eigenspaces of `H = ∇²f(x₀)`.
   - *Convex part.* The convex quadratic part decreases over the first block by at least
     `(σ+1)/(4L)·‖∇φ(x̂_n)‖²`. This is the exact convex silver block bound (`block_descent` at zero weak
     convexity), applied per eigencoordinate. The convex part does not increase over the second block, since all
     silver prefix products are bounded by one (silver non-expansion).
   - *Concave part.* Each step decreases the concave part by at least `α_i‖∇ψ_i‖²/2`, and its gradient norm
     cannot shrink. So the second block pays `σ/(2L)·‖∇ψ_n‖²`.

   On exact quadratics this gives `f(x₀) − f(x_{2n}) ≳ (σ/L)·‖∇f(x_n)‖²` for every spectrum in `[−L, L]`.
   Numerically the constant is about `2`.
2. **Nonlinear perturbation.** The actual iterates are exact gradient descent on the quadratic model plus gradient
   errors `‖e_i‖ ≤ ρ‖x_i − x₀‖²/2`.
   - A Duhamel bound propagates these errors through products of silver steps. Suffix products are at most `1`,
     because the silver schedule is a palindrome and its prefixes are non-expansive.
   - Arbitrary windows are at most `ϱ^{K−2}`: by induction, a window crosses at most one long step.
   - Concave growth is controlled step by step.
3. **Abort rule.** If the gradient exceeds `M·G` inside a cycle, then the travel bound `‖x_i − x₀‖ ≤ 2σMG/L`
   still holds up to that point. The model shows the prefix increased `f` by at most `M²G²/(8L)`. The following
   `1/L` step then decreases `f` by at least `M²G²/(2L)`, which pays for the aborted calls. The binding constraint
   is `16σ²e ≤ MG`, i.e. `16ρε(ϱ^K)^{9/2} ≤ L²`.
4. **Accounting.**
   - Probe steps, completed cycles and aborted cycles each decrease `f` by at least `G²/(2L)` per gradient call.
     This needs `G² = σε²/(25n)` with `σ/n ≍ (ϱ/2)^K`.
   - A potential argument over episodes, together with the level choice, gives the budget.

## Limitations

- **Small exponent, poor constants.** Against plain gradient descent's `2LΔ/ε²`, the stated budget is smaller only
  when `90(ρε/L²)^{1/22} < 2` and `400(LΔ/ε²)^{4/5} < 2LΔ/ε²`. That requires `L²/(ρε) > 45²² ≈ 10³⁶` and
  `LΔ/ε² > 200⁵ ≈ 3·10¹¹`, plus margin for the sum of both terms. The result is an asymptotic statement about the exponent. Constants were not optimized: the
  junction certificate numerically allows a constant about `50×` better than the one used.
- **Method-specific.** This is a gradient-descent-specific contribution, motivated by the stepsize-hedging question.
  It does not improve the best known complexity of the problem class.
- **Knowledge of parameters.** The gating thresholds and the level use `L, ρ, ε, Δ`.
- **No lower bound.** No lower bound for gradient descent with adaptive or predetermined steps on this class is
  proved.
