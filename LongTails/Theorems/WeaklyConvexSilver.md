# Long-step gradient descent on smooth weakly convex functions

Lean theorem: [`WeaklyConvexSilver.lean`](WeaklyConvexSilver.lean) (`OracleTemplate.WeaklyConvexSilverGd.result`).
Setup: [`SmoothWeaklyConvex.lean`](../Setups/SmoothWeaklyConvex.lean).
Algorithm: [`WeaklyConvexSilver.lean`](../Algorithms/WeaklyConvexSilver.lean).

## Problem class and oracle

- **Objective.** A differentiable `f : E → ℝ` on a real Hilbert space with:
  - an `L`-Lipschitz gradient;
  - `ρ`-weak convexity, meaning `f + (ρ/2)‖·‖²` is convex. This is equivalent to `∇²f ⪰ −ρI` for `C²` functions.
  - a lower bound with `f(x₀) − inf f ≤ Δ`.

  These are the standard assumptions for smooth weakly convex ("hypoconvex") minimization. See [Davis–Drusvyatskiy 2019](https://arxiv.org/abs/1803.06523) and [Carmon–Duchi–Hinder–Sidford](https://arxiv.org/abs/1611.00756).
- **Related exact analyses of gradient descent.**
  - [Rotaru–Glineur–Patrinos](https://arxiv.org/abs/2406.17506) give exact worst-case rates for this hypoconvex class. They cover all constant step sizes and a fixed variable-step sequence. Every step there is outside the long-step regime, and every rate is `Θ(LΔ/N)`.
  - [Abbaszadehpeivasti–de Klerk–Zamani](https://arxiv.org/abs/2104.05468) treat fixed step lengths for general `L`-smooth (not necessarily weakly convex) functions.
- **Oracle.** Exact gradients.
- **Target.** A point with `‖∇f(x)‖² ≤ ε²`.
- **Public parameters.** The algorithm knows `L`, `ρ`, `Δ`, `ε` and `x₀`.
- **Allowed algorithms.** The setup restricts them through `gdFamily`. Every query is a gradient-descent step `x_{t+1} = x_t − h_t ∇f(x_t)` with a positive, predetermined step sequence `h_t`. The output is the queried point with the smallest observed gradient norm.

## Algorithm and guarantee

- **Schedule.** The algorithm runs gradient descent with the periodically repeated silver step-size block of level `K`:
  - the block is `SilverSchedule.steps K`, divided by `L`;
  - the block has `2^K − 1` steps with total step length `(ϱ^K − 1)/L`, where `ϱ = 1 + √2`.
- **Choice of `K`.** `K` is the largest level with `250000·ρ·(7/2)^K ≤ L`, capped at the first level with `ϱ^K ≥ 4LΔ/ε²`.
- **Fallback.** If this gives `K ≤ 1`, the method uses the constant step `√2/L`.
- **Output.** The best-gradient iterate.

The theorem proves that `‖∇f(output)‖² ≤ ε²` after

```
⌈32 · L · (ρ/L)^(3/20) · Δ / ε²⌉ + ⌈13 · (L Δ / ε²)^(4/5)⌉ + 3
```

gradient evaluations.

- **First term.** When `ρ/L` is small, the first term improves on the `2LΔ/ε²` gradient calls of plain gradient descent by the factor `(ρ/L)^{3/20}`, i.e. polynomially in `L/ρ`.
- **Second term.** It is the single-block term that remains when `ρ → 0`. For convex `f` it matches, up to constants, the long-step gradient-norm rate `O((LΔ/ε²)^{log_ϱ 2})` of [Grimmer–Shu–Wang 2403.14045](https://arxiv.org/abs/2403.14045), with `log_ϱ 2 ≈ 0.786 ≤ 4/5`. Their schedule differs slightly from the silver schedule of [Altschuler–Parrilo](https://arxiv.org/abs/2309.07879).

## What is new

**Open question addressed.** It was open whether long-step gradient descent can improve on the `Θ(LΔ/ε²)` worst-case complexity of constant-step gradient descent beyond the convex case.
- Altschuler–Parrilo ([2309.07879](https://arxiv.org/abs/2309.07879), concluding discussion) write: "it is less clear if extensions to non-convex settings are also possible. In particular, can one prove accelerated rates for converging to an ε stationary point?"
- The conclusion of Grimmer–Shu–Wang ([2309.09961](https://arxiv.org/abs/2309.09961)) also leaves nonconvex long steps open.
- The exact hypoconvex analyses above cover only non-long-step schedules, and all of them give rates of order `LΔ/N`.

**What we prove.** For `ρ`-weakly convex `L`-smooth functions, gradient descent with a predetermined schedule and best-iterate output needs only `O(L^{1−a} ρ^{a} Δ/ε² + (LΔ/ε²)^{0.8})` gradient calls with `a = 3/20`.
- To our knowledge (literature search up to 2026-10-25), this is the first polynomial improvement in `L/ρ` for gradient descent on this class.
- It interpolates between the convex long-step rate (`ρ = 0`) and the plain gradient-descent rate (`ρ ≳ L`).
- Accelerated methods built on inexact proximal point steps reach `O(√(Lρ)Δ/ε² · log(L/ρ))` (Carmon et al., SIOPT 2018, Lemma 3.1), i.e. exponent `a = 1/2` up to a log factor. Our exponent is 30% of that exponent, and it is obtained with plain gradient steps and no momentum.

**Technical mechanism.**
1. **Block decomposition.** The silver certificate of Altschuler–Parrilo decomposes recursively (`primitive_join` in [`SilverTrace.lean`](../Proofs/SilverTrace.lean)). For weakly convex `f`, each interpolation defect is only bounded below by `−ρ‖y_u − y_v‖²` with `y = x − ∇f/L`. A uniform error bound over the whole block gives an exponent of only about `0.098`.
2. **Virtual anchors.** The new ingredient is localizing these errors with virtual anchors `c = y_e`, where `f_c = f(e) − ‖∇f(e)‖²/2` and `∇f(c) := 0`, taken at the end `e` of a block. For every node `w`, the defect satisfies `d(c, w) = d(e, w)` exactly.
3. **Induction over the block tree.** It carries an "inexact convexity" condition `f_end ≥ f_c − t·S·‖∇f_end‖² − η` with `t = 1/10`. This propagates to left children (IC propagation) and yields nonexpansion of the long step.
4. **Scale decay.** The right child `R` of every block has its own anchor radius `σ_R² ≤ θ² r²`, with `θ² = 2/5` at levels `≥ 3` and `3/5` below. This is proved by an explicit six-multiplier SOS certificate in [`WeaklyConvexSilverCertificate.lean`](../Proofs/WeaklyConvexSilverCertificate.lean). Its residual is a concave quadratic in `1/(S+1)`, so three constant Gram matrices certify all levels.
5. **Accumulated error.** The scale decay keeps the primitive error at `ρ·O((1 + ϱ²θ²)^K)` instead of `ρ·O((2 + 2ϱ)^K)`. The block bound `‖∇f(x_end)‖² ≤ 4L(f(x_start) − f(x_end))/ϱ^K` then holds whenever `(ρ/L)(7/2)^K ≤ 1/250000`, since `1 + 2ϱ²/5 < 7/2`.
6. **Exponent.** The exponent `3/20` comes from `(ϱ/2)^{20} ≥ (7/2)^3`.

## Exponents and limitations

| Exponent | Value | Status |
|---|---|---|
| Formal theorem | `a = 3/20` | Proved in Lean. |
| Same argument with `Γ₊ ↓ 1 + 2ϱ²/5` | `a* = ln(ϱ/2)/ln(1+2ϱ²/5) ≈ 0.1564` | Not formalized. |
| Numerical PEP block gains (numerical evidence only) | `≈ 0.2136 = 1 − 1/log₂ϱ` | Conjectured sharp. The proof loses exponent by compounding the worst-case decay `θ` at each right turn, with no decay at left turns. |

**Constants.** The constants are poor:
- The formal smallness condition `(ρ/L)(7/2)^K ≤ 1/250000` comes from crude error bookkeeping. A numerical solve of the same recursion supports about `10⁻³`.
- With the stated budget, the guarantee beats the plain gradient-descent bound `2LΔ/ε²` only when `ρ/L ≲ 10⁻⁸`.
- The result is an asymptotic statement in `L/ρ`.

**Method-specific scope.** The result is specific to gradient descent with predetermined step sizes. The best known complexity for the problem class is `Õ(√(Lρ)Δ/ε²)`, achieved by accelerated methods.

**Parameter use.** The algorithm knows `L`, `ρ`, `Δ` and `ε`. It uses `Δ` and `ε` only to cap the level, which amounts to knowing the horizon, as with all silver schedules. The cap keeps the budget finite as `ρ → 0`.

**No lower bound.** No lower bound is proved for gradient descent with arbitrary schedules on this class, so the optimal exponent is open.
