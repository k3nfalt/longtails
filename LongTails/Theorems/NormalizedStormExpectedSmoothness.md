# Variance reduction without bounded variance: normalized STORM under expected-smoothness (ABC) noise

## Summary

Variance-reduced methods such as STORM and SPIDER find an ε-stationary point of a smooth nonconvex
expectation `F(x) = E_ξ f(x, ξ)` with `O(ε⁻³)` stochastic gradients. This needs mean-squared
smoothness (MSS) and **uniformly bounded variance**. SGD, by contrast, has a mature theory beyond
bounded variance, namely the *expected smoothness*/ABC condition of Khaled–Richtárik, but only at the
`O(ε⁻⁴)` rate.

This result shows that, under MSS, the ε⁻³ rate survives when the gradient-noise variance is allowed
to grow with the suboptimality `F(x) − F_low`, with no bounded-variance assumption at all. A natural
consequence: for **nonnegative losses whose sample functions are L-smooth**, normalized STORM reaches
`E‖∇F(x_out)‖ ≤ ε` with

  `O(L F(x₀)/ε² + L^{3/2} F(x₀)^{3/2}/ε³)`

pair calls and no assumption on the noise. To our search, only SGD-type `O(ε⁻⁴)` guarantees were
previously available for this class.

This sits next to a recent negative result. When the variance instead grows with the *distance*
`‖x − x₀‖` (Blum–Gladyshev noise), the complexity under MSS is `Θ(ε⁻⁴)` (Fazla et al. 2026). Variance
tied to function values is benign for variance reduction; variance tied to distance is not.

## Setup

[`LongTails/Setups/ExpectedSmoothnessNonconvex.lean`](../Setups/ExpectedSmoothnessNonconvex.lean)
(`LongTails.Setups.ExpectedSmoothnessNonconvex.spec`).

**Space.** `E` is a real, complete inner-product space with Borel σ-algebra and second-countable
topology; arbitrary finite dimension and separable Hilbert spaces are covered.

**Objective.** `f : E → ℝ` is differentiable with an `L`-Lipschitz gradient. There is a number
`lower ≤ f(x)` for all `x`, with `f(x₀) − lower ≤ Δ`.

**Oracle.** IID samples `ξ_k ∼ p` (the repository's `IID` structure). One call with query `(x, y)`
returns `(g(x, ξ_k), g(y, ξ_k))`, i.e. two stochastic gradients on the *same* sample. This is the
standard STORM/SPIDER model. The oracle `g` is jointly measurable, integrable and unbiased:
`∫ g(x, ω) dp = ∇f(x)`.

**Mean-squared smoothness.** `∫ ‖g(x,ω) − g(y,ω)‖² dp ≤ L² ‖x − y‖²`. This is Arjevani et al. 2019,
eq. (4), and the STORM/SPIDER assumption, here with the same constant `L`. MSS implies that `∇f` is
`L`-Lipschitz by Jensen, so the separate smoothness hypothesis adds no restriction.

**Expected-smoothness (ABC) variance.** With the same `lower`:

  `∫ ‖g(x,ω) − ∇f(x)‖² dp ≤ 2A (f(x) − lower) + C`   for all `x`,

where `A, C ≥ 0`. No bounded-variance assumption is made.

**Accuracy criterion.** `E‖∇f(x_out)‖ ≤ ε`, a first moment, with the expectation over the
algorithm's seed and all oracle samples.

**Cost.** Number of oracle calls. Each call is one sample and two gradient evaluations.

### Provenance and scope of the assumptions

- **The ABC condition.** It is Assumption 2 ("ES") of Khaled & Richtárik,
  [*Better Theory for SGD in the Nonconvex World*](https://arxiv.org/abs/2002.03329)
  (TMLR 2023; arXiv v3).
  - Their form bounds the second moment, `E‖g‖² ≤ 2A(f − f_inf) + B‖∇f‖² + C`.
  - It is equivalent to the variance form above up to `B ← B − 1`.
  - The `B‖∇f‖²` term is absorbed into `A`, because `‖∇f(x)‖² ≤ 2L(f(x) − lower)` for `L`-smooth `f`
    bounded below by `lower`. So the stated form loses no generality.
  - It contains *affine variance* `σ₀² + σ₁²‖∇f‖²` (Faw et al., COLT 2022; Attia–Koren, ICML 2023) as
    the special case `A = Lσ₁², C = σ₀²`.
  - Using an arbitrary lower bound `lower ≤ inf f` instead of `inf f` gives a weaker assumption, at the
    price of a larger `Δ`.
- **MSS and the same-sample pair oracle** are exactly those of STORM (Cutkosky–Orabona, NeurIPS 2019)
  and SPIDER (Fang et al., NeurIPS 2018).
- **The single change** relative to the STORM setting is *bounded variance → ABC variance*.

### Natural instances (no variance assumption needed)

- **Nonnegative L-smooth sample losses.** If every `f(·, ξ)` is nonnegative and `L`-smooth, then
  `‖∇f(x, ξ)‖² ≤ 2L f(x, ξ)` pointwise. Hence `E‖g − ∇F‖² ≤ E‖g‖² ≤ 2L F(x)`: the ABC condition holds
  with `A = L, C = 0, lower = 0`, and MSS holds with constant `L`. This is Khaled–Richtárik's
  Proposition 2 with `lower = 0`. The bounded variance typically fails, as in the following examples.
  - **Single-index regression with a softplus link**, `f(x; a, y) = (softplus⟨a, x⟩ − y)²` with
    `‖a‖ ≤ R`. It is nonconvex and coordinates interact through `a`. The Hessian
    `2(σ(⟨a,x⟩)² + (softplus⟨a,x⟩ − y)σ'(⟨a,x⟩)) a aᵀ` is bounded. The gradient grows linearly in
    `‖x‖`, so the variance grows like `‖x‖²`.
  - **Random-design least squares plus a bounded smooth nonconvex penalty**, e.g.
    `½(⟨a,x⟩ − y)² + λ Σᵢ xᵢ²/(1 + xᵢ²)`. The variance grows like `‖x‖²` because of the multiplicative
    design noise.
  - **Robust regression** with nonnegative, smooth, nonconvex losses of quadratic growth.
  - **Subsampled ERM** (minibatches, importance or arbitrary sampling) over any nonnegative smooth
    losses.
- **Quadratic diagnostic.** For `f(x, ξ) = ½ xᵀH_ξ x` with random PSD `H_ξ`, `‖H_ξ‖ ≤ L`, the variance
  `E‖(H_ξ − H̄)x‖²` is unbounded but at most `2L F(x)`.

## Algorithm and output

[`LongTails/Algorithms/NormalizedStorm.lean`](../Algorithms/NormalizedStorm.lean)
(`OracleTemplate.NormalizedStorm.normalizedStorm`). It is normalized STORM with an initial
minibatch.

1. **Initial batch.** Make `b₀` calls at `(x₀, x₀)` and set `d₀` to the running mean of the first
   components.
2. **Iterations.** For `t = 0, 1, …`:
   - `x_{t+1} = x_t − (η/‖d_t‖) d_t` (no step when `d_t = 0`);
   - query `(x_{t+1}, x_t)` on a fresh sample `ξ` and set
     `d_{t+1} = g(x_{t+1}, ξ) + (1 − a)(d_t − g(x_t, ξ))`.
3. **Output.** The seed is `τ`, uniform on `{0, …, T}`. The algorithm performs `τ` iterations, ignores
   any remaining calls, and outputs `x_τ`. This is a uniformly random iterate among `x₀, …, x_T`.

**Parameters.** The tuning is explicit and uses only the public parameters:

- `S = 4AΔ + 2Aε²/L + C`
- `a = ε²/(ε² + 400 S)`
- `η = ε√a/(40L)`
- `b₀ = ⌈192 S/ε²⌉ + 1`
- `T = ⌈80LΔ/(ε²√a)⌉`

## Main theorem

[`LongTails/Theorems/NormalizedStormExpectedSmoothness.lean`](NormalizedStormExpectedSmoothness.lean),
`OracleTemplate.NormalizedStorm.result : Convergence spec budget`. The budget is

```
⌈(192(4AΔ + C) + 80LΔ)/ε² + 384A/L + 1600 L Δ √(4AΔ + 2Aε²/L + C)/ε³⌉ + 3
```

With this many calls, the output satisfies `E‖∇f(x_out)‖ ≤ ε`. In order notation:

  `O( (LΔ + AΔ + C)/ε² + A/L + LΔ √(AΔ + C)/ε³ + Δ√(AL)/ε² )`.

- **`A = 0` (bounded variance `σ² = C`).** This is the known STORM/SPIDER rate
  `O(LΔ/ε² + σ²/ε² + LΔσ/ε³)`, which is optimal by Arjevani et al. (2019).
- **Nonnegative L-smooth samples** (`A = L, C = 0, Δ = F(x₀)`). This gives
  `O(L F(x₀)/ε² + L^{3/2}F(x₀)^{3/2}/ε³)`.

The Lean proof (all modules compile; the comparator audit accepts with axioms `propext`,
`Classical.choice`, `Quot.sound`) is split as follows:

- **[`NormalizedStormTrajectory`](../Proofs/NormalizedStormTrajectory.lean).** Trajectory, prefix
  dependence, measurability, and identification of `execute` with the mathematical recursion,
  counting every call.
- **[`NormalizedStormOrthogonality`](../Proofs/NormalizedStormOrthogonality.lean).** The
  fresh-sample orthogonality lemma `E‖c U + W‖² ≤ c² E‖U‖² + E w`. It requires only a *conditional*
  second-moment bound `w` that is integrable along the trajectory, not a uniform bound.
- **[`NormalizedStormMoments`](../Proofs/NormalizedStormMoments.lean).** Normalized descent,
  minibatch error, and the one-step STORM error recursion.
- **[`NormalizedStormDescent`](../Proofs/NormalizedStormDescent.lean).** The self-bounding
  induction and the telescoped gradient bound.
- **[`NormalizedStormConvergence`](../Proofs/NormalizedStormConvergence.lean).** Tuning and budget
  algebra, and assembly over the uniform output index.

## Mathematical mechanism

Write `e_t = d_t − ∇F(x_t)` and `D_t = E[F(x_t) − lower]`. The proof rests on three facts.

1. **Pathwise normalized descent:**
   `F(x_{t+1}) ≤ F(x_t) − η‖∇F(x_t)‖ + 2η‖e_t‖ + Lη²/2`.
2. **Error recursion with function-value-dependent noise.** Fresh-sample orthogonality,
   unbiasedness, MSS and the ABC bound at the *new* iterate give

   `E‖e_{t+1}‖² ≤ (1−a)² E‖e_t‖² + 2a²(2A D_{t+1} + C) + 8L²η²`.

   This uses the ABC bound only through its conditional expectation. That is valid because the bound
   is *affine* in `F(x_{t+1})`, so it passes through the outer expectation.
3. **Self-bounding induction.** Fix `V = ε²/64` and `D_max = 2Δ + ε²/L`. The induction maintains
   `E‖e_s‖² ≤ V` and `D_s ≤ Δ + s(2η√V + Lη²/2) ≤ D_max` for all `s ≤ T + 1`, jointly with the
   integrability of every quantity.
   - The descent step needs the error bound up to time `t`.
   - The error step at `t + 1` needs `D_{t+1} ≤ D_max`.
   - The horizon `(T + 1)η ≈ 2Δ/ε` makes the accumulated drift `O(Δ)`.

   Hence the effective variance is `σ_eff² = 2A D_max + C = S`, and the standard STORM tuning applies
   with `σ² ← S`.

### Why the obvious reductions fail

- **Bounded variance on a ball.** Normalized iterates satisfy `‖x_t − x₀‖ ≤ ηT = Θ(Δ/ε)`
  deterministically. But MSS plus ABC only gives variance growth `≲ L²‖x − x₀‖²` on that ball (a
  Blum–Gladyshev bound). That yields `σ_ball = Θ(LΔ/ε)` and the STORM bound `LΔσ_ball/ε³ = Θ(ε⁻⁴)`.
  This is precisely the regime where Fazla et al. prove a `Θ(ε⁻⁴)` lower bound.
- **Sublevel sets.** The iterates stay in a sublevel set only *in expectation*, never almost surely.
  The existing bounded-variance STORM theorems require a uniform (conditional) bound and do not apply.
- **SGD under ABC.** It has the `ε⁻⁴` rate (below); minibatching does not change the exponent.

## Comparison with the closest results

All comparisons use the same criterion, `E‖∇F‖ ≤ ε` or `min_k E‖∇F(x_k)‖ ≤ ε`.

| Result | Noise assumption | Smoothness / oracle | Complexity |
|---|---|---|---|
| Khaled–Richtárik 2023, Cor. 1 (SGD) | ABC (ES) | `L_F`-smooth, one query | `O(L_FΔ·max{B, AΔ/ε², C/ε²}/ε²)`; leading term `O(L_FΔ(AΔ + C)/ε⁴)` |
| STORM / SPIDER (Cutkosky–Orabona 2019; Fang et al. 2018) | bounded variance σ² | MSS, pair query | `O(LΔ/ε² + σ²/ε² + LΔσ/ε³)` |
| Fazla et al. arXiv 2604.16620; Upadhyay et al. arXiv 2605.15314 | Blum–Gladyshev (variance ∝ distance) | MSS, pair query | `Θ(ε⁻⁴)` (lower bound + normalized STORM) |
| Ada-STORM (arXiv 2406.01959v2), META-STORM (arXiv 2209.14853) | bounded variance | MSS | `O(ε⁻³)` (adaptive) |
| **This result** | **ABC (variance ∝ suboptimality)** | **MSS, pair query** | **`O((LΔ + AΔ + C)/ε² + A/L + LΔ√(AΔ+C)/ε³)`** |

**Improvement regime.** The setup uses one constant `L` both for the smoothness of `F` and for MSS. In
general, `F` is `L_F`-smooth with `L_F ≤ L` (MSS implies `L_F ≤ L` by Jensen), and SGD's bound depends
only on `L_F`. Under the same ABC condition (SGD is also given MSS, which it cannot use), SGD's leading
term is `L_FΔ(AΔ + C)/ε⁴`, while ours is `LΔ√(AΔ + C)/ε³`.
- **General case.** The gain factor is `≍ (L_F/L)·√(AΔ + C)/ε`. It is unbounded as `ε → 0`, but it
  appears only for `ε ≲ (L_F/L)√(AΔ + C)`.
- **Nonnegative L-smooth samples.** The factor is `≍ (L_F/L)√(L F(x₀))/ε`.
- **Why MSS is needed.** Without MSS, `ε⁻⁴` cannot be improved even with bounded variance (Arjevani et
  al.). So the result uses the same oracle model as STORM and weakens one assumption.
- **Not covered.** A sharper statement with separate constants (`L_F` in the `ε⁻²` terms, `L` only in
  the `ε⁻³` term), as in standard STORM bounds, is not formalized here.

**Novelty status.** As far as our searches found, this is the first `ε⁻³`-type guarantee for variance
reduction under ES/ABC noise in the online (expectation) setting.

- **Found to assume bounded variance:** Ada-STORM, META-STORM, the online variants of PAGE, MARINA
  and DASHA.
- **Use ABC/ES only for SGD-type methods:** the Blum–Gladyshev papers, which cite ES/ABC (Khaled–
  Richtárik; Gorbunov–Hanzely–Richtárik 2020; Ilandarideva et al. 2023).
- **Finite-sum or convex problems:** the Richtárik-group arbitrary-sampling variance-reduction
  analyses we know of. Finite sums never need a variance bound, because they compute full gradients.

This is a gap inferred from theorem scopes, not an explicitly posed open problem. Our searches
(about eight targeted queries plus reading the papers listed) may have missed a remark in a
finite-sum arbitrary-sampling paper.

## Limitations

- **The technique is light.** It is the standard normalized-STORM analysis plus a self-bounding
  induction that controls `E[F(x_t)]`. The contribution is the guarantee and the separation from
  distance-dependent noise, not a new estimator.
- **No matching lower bound in `A` is proved.**
  - For `A = 0`, the bound inherits Arjevani et al.'s `Ω(LΔσ/ε³)`.
  - For `C = 0`, the Arjevani instance violates the ABC condition late in the chain, because the noise
    stays fixed while `F − F_low → 0`. So `Ω(Δ^{3/2}√(AL)/ε³)` is *not* established, and a method that
    exploits decaying noise could conceivably do better.
- **Parameter knowledge.** The tuning uses `L, A, C, Δ, ε`. The guarantee is in expectation, for a
  uniformly random iterate. Constants are not optimized, and the additive `A/L` term comes from the
  integer slack in the horizon.
- **Oracle model.** It requires the same-sample pair oracle and MSS, like every `ε⁻³` method. Each call
  costs two gradient evaluations. Generalized-smoothness growth of the MSS constant is not covered.
