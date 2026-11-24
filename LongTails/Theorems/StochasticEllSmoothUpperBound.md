# Stochastic nonconvex optimization under generalized smoothness of order ρ < 2: upper bound

The [main theorem](StochasticEllSmoothUpperBound.lean) proves an expected-stationarity oracle bound for
stochastic gradient methods on the class of [`StochasticEllSmoothNonconvex`](../Setups/StochasticEllSmoothNonconvex.lean),
using the algorithm [`StochasticEllSmoothMedoid`](../Algorithms/StochasticEllSmoothMedoid.lean). It is the upper half
of a pair. The companion [lower bound](StochasticEllSmoothLowerBound.md) shows that the bound is optimal up to one
logarithmic factor, a factor depending on how close ρ is to 2, and a constant depending only on `p`.

## Setup

The objective `f : E → ℝ` is defined on an arbitrary complete real inner-product space `E`. It satisfies:

- `∇f` exists everywhere and is differentiable;
- generalized smoothness `‖∇²f(x)‖ ≤ ℓ(‖∇f(x)‖)` for all `x` (Li, Qian, Tian, Rakhlin, Jadbabaie, NeurIPS 2023,
  [arXiv:2306.01264](https://arxiv.org/abs/2306.01264), Definition 2 and Assumption 2; Tyurin, ICML 2025,
  [arXiv:2412.11773](https://arxiv.org/abs/2412.11773), Assumption 3.1);
- `ℓ` is *regular of order* `ρ ∈ [0, 2)`: it is nondecreasing on `[0,∞)`, positive on `(0,∞)`, and
  `ℓ(v)u^ρ ≤ ℓ(u)v^ρ` for `0 < u ≤ v`. This is the repository's `EllSmoothNonconvex.Regular` from PR #244.
  It holds for `ℓ(u) = L₀ + L_ρ u^ρ`, so the class contains every `L`-smooth function (ρ = 0), every
  `(L₀,L₁)`-smooth function (ρ = 1), and the `(ρ, L₀, L_ρ)` family of Li et al. for every `ρ < 2`. This is the
  sub-quadratic case (`ρ < 2`) in which Li et al. prove that GD and SGD converge.
- `f(x₀) − f(x) ≤ Δ` for all `x`, as in PR #244.

The oracle returns only a stochastic gradient. It gives `g(x, ξ_k)` with IID samples `ξ_k` (the repository's `IID`
structure), `g` jointly measurable, unbiased (`∫ g(x,·) = ∇f(x)`), and with bounded central `p`-th moment
`∫ ‖g(x,·) − ∇f(x)‖^p ≤ σ^p` for some `p ∈ (1, 2]`. At `p = 2` this is the usual bounded-variance assumption of
Ghadimi–Lan and Arjevani et al. For `p < 2` it is the standard heavy-tailed `p`-BCM model (Zhang et al. 2020;
Liang–Luo 2026). No sub-Gaussian, bounded-noise, symmetry, or samplewise-smoothness assumption is made.

The success criterion is expected stationarity of a single measurable output: `E‖∇f(x̂)‖ ≤ ε`.

## Algorithm and output

The algorithm is `StochasticEllSmoothMedoid.algorithm`. Write `T̄ = Δℓ(ε)/ε²` and `r = p/(p−1)`. The run has
`T = ⌊72 T̄⌋ + 1` rounds. In every round, at the current point `x`:

1. It draws `(2K+2)·n` fresh samples at `x` and forms `2K+2` block means of size `n`, where
   `n = ⌈(2¹⁶σ/ε)^r⌉ + 1` and `K = ⌈64 log₂(2+T̄)/(2−ρ)⌉`.
2. It takes their medoid `v`, the block mean minimizing the sum of distances to the others (repository
   `MultiplicativeRobustEstimator.medoid`).
3. It updates:
   - if the run is already frozen, nothing changes;
   - if `‖v‖ ≤ ε/2`, the run freezes at `x`;
   - otherwise it moves to `x − v / (2ℓ(3‖v‖))`.

The output is the frozen point, or `x₀` if the run never froze. The method uses `ℓ, ρ, p, σ, Δ, ε, x₀`. It does not
use the objective, function values, a minimizer, or an upper bound on gradient norms along the trajectory.

## Guarantee and oracle cost

For every valid parameter tuple and every admissible instance, the output satisfies `E‖∇f(x̂)‖ ≤ ε`. The number of
oracle calls is at most

```
⌈2¹⁵ · (1 + T̄) · (1 + (2¹⁶σ/ε)^(p/(p−1))) · log₂(2 + T̄) / (2 − ρ)⌉,   T̄ = Δℓ(ε)/ε².
```

At `p = 2` the noise factor is `1 + 2³²σ²/ε²`. For `ℓ(u) = L₀ + L_ρu^ρ` we have
`T̄ = L₀Δ/ε² + L_ρΔ/ε^(2−ρ)`.

## Proof idea and the new mechanism

The difficulty is specific to `ρ > 1`. For such `ℓ`, the gradient-norm ODE `u' = ℓ(u)` blows up in finite time. The
distance over which a gradient of norm `u` is guaranteed to stay controlled is `∫_u^∞ dv/ℓ(v) ≍ u/((ρ−1)ℓ(u))`,
which shrinks as `u` grows. A step computed from an estimate that underestimates `‖∇f(x)‖` can therefore cross this
radius, after which the class allows an arbitrarily large gradient and function value. This is why Tyurin (ICML 2025,
§9) assumes sub-Gaussian noise: "light tails … is necessary for handling the non-constant, gradient-dependent step
sizes". It is also why Li et al. (NeurIPS 2023, Theorem 5.3) use a conservative constant step `1/ℓ(2G)`, with `G`
bounding gradients on an enlarged sublevel set. Under bounded variance, a plain batch mean underestimates a gradient
of norm `u` with probability as large as `σ²/(b u²)`, so neither approach gives an `ℓ(ε)` rate.

The proof has five steps.

1. **Safe inexact step** (`StochasticEllSmoothStep.inexact_descent`). If `‖v − ∇f(x)‖ ≤ ‖v‖/4`, the step
   `x − v/(2ℓ(3‖v‖))` decreases `f` by at least `‖v‖²/(8ℓ(3‖v‖))`. The proof fences the gradient along the segment,
   as in PR #244's exact-gradient lemma. Regularity turns this into a decrease of at least `ε²/(72ℓ(ε))` whenever
   `‖v‖ > ε/2`. Only absolute accuracy `ε/8` is needed, at every gradient level.
2. **Heavy-tailed block means** (`StochasticEllSmoothEstimator.block_mean_first_moment`). Truncation at level
   `n^{1/p}σ` gives `E‖mean − ∇f(x)‖ ≤ 3σ n^{−(p−1)/p}` under the `p`-th-moment assumption alone.
3. **Medoid confidence and tail** (`medoid_estimate`). The medoid of `2K+2` block means fails accuracy `ε/8` with
   probability at most `2^{−(2K+2)}`. The repository's medoid second-moment bound,
   `E‖medoid − u‖² ≤ 4608 (E‖mean − u‖)²`, needs only first moments of the blocks. Combined with Cauchy–Schwarz it
   bounds the excess error `E[err·1{err > ε/8}]` by `(ε/176)·2^{−(K+1)}`. This controls the case where the run freezes
   on a wrong estimate.
4. **Bounded harm on failure** (`StochasticEllSmoothRun.output_bound`). Pointwise, the output satisfies
   `‖∇f(x̂)‖ ≤ ε/2 + ε/8 + Σ_t err_t·1{err_t > ε/8} + G₀·1{some round inaccurate}`, where
   `G₀ = ε(1 + (16T̄)^{1/(2−ρ)})`.
   - The fallback output `x₀` has bounded gradient `‖∇f(x₀)‖ ≤ G₀`, by `initial_gradient_bound`. This follows from
     `f(x₀) − inf f ≤ Δ` and the regularity of `ℓ` with `ρ < 2`.
   - Freezing at a point keeps that point forever, so a frozen output's gradient is controlled by the estimate made
     when it froze.
5. **Adapted sums over IID blocks** (`adapted_sum`, `adapted_union`). These bound the expectations, with no union over
   unbounded harms.

The logarithmic factor in `K` is the price of making catastrophic rounds rare, at rate `≲ ε/(T G₀)`, while the
fallback caps their harm.

## Comparison with prior work

All rates are stated for the target `‖∇f(x̂)‖ ≤ ε`.

| Result | Assumptions | Guarantee | Complexity |
|---|---|---|---|
| Tyurin, ICML 2025, [arXiv:2412.11773](https://arxiv.org/abs/2412.11773) (v-latest 27 Jun 2025), Thm 9.2 | sub-Gaussian noise (Assumption 9.1), any `ℓ` (here `ρ ≤ 2`) | min-iterate, w.p. `1−δ` | `Θ̃((1+σ²/ε²)·Δℓ(ε)/ε²)·log(T/δ)` |
| Li et al., NeurIPS 2023, [arXiv:2306.01264](https://arxiv.org/abs/2306.01264) v2, Thm 5.3 | bounded variance, `ρ < 2` | `(1/T)Σ‖∇f(x_t)‖² ≤ ε²` w.p. `1−δ` | `T ≳ max{2ℓ(2G)F/ε², 16G²F²/ε⁴}` with `F = 8(Δ+σ)/δ`, `G = sup{u : u² ≤ 2ℓ(2u)F}` (so `G² = 2ℓ(2G)F`) |
| Clipped AdaGrad, [arXiv:2609.30276](https://arxiv.org/abs/2609.30276) v1, Thm 1/Thm 2 (preprint) | bounded variance, `ρ < 2` | `(1/T)Σ‖∇f(x_t)‖² = O(d(√log T + log(1/δ))/√T)` w.p. `1−δ` | `Õ(d²ε⁻⁴)`; step/clip conditions (their (A.6)) involve `d`, `L° = ℓ(2G°)`, `V° = (G°)²+σ²` with `G°` the gradient bound on `{f ≤ f* + 2Δ}` |
| Adam under `L₀`–`L_p` smoothness, [arXiv:2609.37787](https://arxiv.org/abs/2609.37787) v2 (preprint) | second-moment (ABC) noise | high probability with polynomial `1/δ` (expectation only for `p < 1`) | Adam-specific, `d`-dependent |
| Liang–Luo, [arXiv:2610.21692](https://arxiv.org/abs/2610.21692) v2 (preprint) | `ρ = 1` only, `p`-BCM | expectation | tight `Θ((1+(σ/ε)^{p/(p−1)})(L₀Δ/ε² + L₁Δ/ε))` (lower bound for arbitrary randomized first-order algorithms) |
| Normalized methods under BG-0 noise, [arXiv:2605.15314](https://arxiv.org/abs/2605.15314) v2 | symmetric generalized smoothness (order ≤ 1) | expectation | different noise model |
| **This theorem** | `p`-BCM noise, any regular `ℓ` with `ρ < 2` | expectation, single output | `O((1+T̄)(1+(2¹⁶σ/ε)^{p/(p−1)})·log₂(2+T̄)/(2−ρ))` |

What is new:

- **First `ℓ(ε)`-rate without light tails for `ρ ∈ (1,2)`.** In expectation, for a single output and up to
  one logarithm, this answers the question Tyurin raises in §9 and §10: extending gradient-dependent step sizes under
  ℓ-smoothness beyond light-tailed noise. His Theorem 9.2 is a high-probability min-iterate statement under
  sub-Gaussian noise, so the criteria differ. Our result holds for bounded variance and for heavy tails (`p < 2`).
- **Comparison with the bounded-variance baselines.** Li et al. and 2609.30276 control the trajectory through the
  sublevel gradient bound `G`, so their complexities depend on `ℓ(2G)` and `G`, not on `ℓ(ε)`.
  - In Li et al., the `ε⁻⁴` coefficient is `16G²F² = 32ℓ(2G)F³` with `F = 8(Δ+σ)/δ`. Ours is `≍ Δℓ(ε)σ²` up to
    the log and the `p`-dependent constant.
  - For the `(ρ,L₀,L_ρ)` family, `G ≍ max{√(L₀F), (L_ρF)^{1/(2−ρ)}}`. Their leading term then contains
    `L_ρ G^ρ F³`, which is polynomially larger than our `(L₀ + L_ρε^ρ)Δσ²` when `L_ρ > 0` and `ε` is small. It also
    carries the factor `δ⁻³`.
  - 2609.30276 additionally has a dimension factor.
  - These are not like-for-like comparisons. Both baselines are high-probability statements about the average of
    `‖∇f(x_t)‖²`; ours is an expectation for one output. We claim the better dependence on `ℓ`, `d` and the
    problem constants, not a uniform domination.
- **Generalization of Liang–Luo** from `ρ = 1` to every `ρ < 2`, at the price of a `log₂(2+T̄)/(2−ρ)` factor.
  At `ρ = 1` our bound is worse than theirs by this logarithm.

What is not new:

- The step `1/(2ℓ(3‖v‖))` is a variant of Tyurin's and PR #244's closed-form step.
- Median-of-means and medoid estimators, truncation for heavy-tailed means, and validation-type output rules are
  standard ingredients. The contribution is their combination with the finite-blow-up radius and the bounded-harm
  fallback, and the resulting `ℓ(ε)` rate.

## Limitations

- **One logarithmic factor.** The upper bound carries `log₂(2+T̄)/(2−ρ)`, which is absent from the lower bound. Its
  source is the per-round confidence `≲ ε/(T G₀)`. We do not know whether a logarithm is necessary for `ρ ∈ (1,2)`
  under bounded variance. Liang–Luo show it is not needed at `ρ = 1`. The factor appears even when `0 < σ ≪ ε`. At
  `σ = 0` the method is still valid, but deterministic GD (PR #244) is log-free.
- **`p`-dependent constants.** The constant `2^{16 p/(p−1)}` hidden in `(2¹⁶σ/ε)^{p/(p−1)}` blows up as `p → 1`. For
  fixed `p` it is a constant; uniformly in `p` it is not. Constants were not optimized.
- **Expected accuracy only.** No high-probability statement is formalized. The same algorithm with `K ≍ log(T/δ)` gives
  a `1−δ` guarantee, but this is not part of the theorem.
- The algorithm needs `ℓ, ρ, p, σ, Δ, ε`. It is not parameter-free.
- `ρ = 2` is excluded: the fallback bound `G₀` and the lower bound both need `ρ < 2`.

## Instances beyond (L₀,L₁)

Take unit-cone vectors `a_i` with `⟨a_i, e⟩ ≥ κ‖a_i‖` and set

`f(x) = Σ_i exp(exp(a_iᵀx − b_i)) + Σ_j c_j cos(w_jᵀx)`,

in any dimension, with interacting coordinates. Write `h(t) = e^{e^t}`. Then `h'' = h'(1+e^t)` and
`e^t ≤ 1 + log(1+h')`. Since all `h' > 0` and the `a_i` lie in a cone, `‖∇f₁‖ ≥ κ Σ h'_i ‖a_i‖`. The bounded cosine
part shifts the gradient norm by at most a constant. Together these give `‖∇²f‖ ≤ C₀ + C₁(u + C₂) log(e + u + C₂)` at
gradient norm `u`. That is at most `L₀ + L_ρ u^ρ` for every `ρ ∈ (1,2)`, with suitable constants. The function is
bounded below and nonconvex for large `|c_j|`. It is not `(L₀,L₁)`-smooth for any constants, because `h''/h'` is
unbounded.

A motivating model is Weibull survival regression with a log-parametrized shape. The term `(t/λ)^{e^θ}` is
doubly exponential in `θ` when `t > λ`, so its curvature grows like `u·log u` in the gradient norm `u`. We give this
one-dimensional calculation as motivation only; we do not claim a multivariate verification for that model.

## Scope (task requirements)

- **Important, popular setup.** Generalized smoothness is widely studied. `(L₀,L₁)`-smoothness (`ρ = 1`) was
  motivated by language-model training (Zhang et al. 2020), and stochastic and heavy-tailed gradients are its main use
  case. For `ρ = 1` the tight stochastic bound is Liang–Luo's, which our upper bound does not improve.
  - **What is new here.** The new territory is the general sub-quadratic class `ρ ∈ (1,2)` of Li et al. (NeurIPS
    2023) and Tyurin (ICML 2025). It includes curvature growing like `u log u` (double exponentials). For this class,
    the stochastic complexity was open beyond light tails.
  - **What we do not claim.** We do not claim specific language-model relevance for `ρ > 1`.
- **Almost tight upper and lower bounds in Template/TemplateLowerBound terms.** This theorem is the `Convergence`
  half. The `NonConvergence` half is [StochasticEllSmoothLowerBound](StochasticEllSmoothLowerBound.md). The gap is
  stated above and in the lower-bound note.
- **Overlap.** This is distinct from PR #244 (deterministic oracle), PR #229/#149 (`ℓ ≡ L`), and open PR #215
  (minimax).

## Lean

- **Setup:** [`StochasticEllSmoothNonconvex`](../Setups/StochasticEllSmoothNonconvex.lean).
- **Algorithm:** [`StochasticEllSmoothMedoid`](../Algorithms/StochasticEllSmoothMedoid.lean).
- **Proofs:**
  - [`StochasticEllSmoothStep`](../Proofs/StochasticEllSmoothStep.lean): safe inexact step and the `x₀` gradient
    bound.
  - [`StochasticEllSmoothEstimator`](../Proofs/StochasticEllSmoothEstimator.lean): truncation and the medoid.
  - [`StochasticEllSmoothRun`](../Proofs/StochasticEllSmoothRun.lean): trajectory, output bound, and adapted sums.
  - [`StochasticEllSmoothUpper`](../Proofs/StochasticEllSmoothUpper.lean): execution, parameters, budget, and
    assembly.
- **Execution:** the theorem is proved for the actual `OracleTemplate.execute` run. Every oracle call is counted:
  `T(2K+2)n ≤ budget`.
