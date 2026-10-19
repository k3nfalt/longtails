# Variance reduction under strong growth and affine variance: `Γ²` becomes `Γ`

## Summary

Take a smooth nonconvex expectation `F(x) = E_ξ f(x, ξ)` whose stochastic gradients have **affine
variance**:

  `E‖g(x, ξ) − ∇F(x)‖² ≤ Γ² ‖∇F(x)‖² + Λ²`.

When `Λ = 0` this is the **strong growth condition** with `ρ = 1 + Γ²`, the standard model of
interpolation or over-parameterization. SGD then needs `Θ((1 + Γ²) L Δ / ε²)` gradients for
`E‖∇F‖ ≤ ε`.

**Prior variance-reduction analyses.**
- Under the variance-reduction assumption (mean-squared smoothness, MSS, with constant `L̄` and the
  same-sample pair oracle), the published analysis is SPIDER under affine variance (Chen et al.,
  ICML 2023).
- Even with optimal minibatching, that analysis gives `(Γ²L + ΓL̄)Δ/ε²` at `Λ = 0`. This is never
  better than SGD.
- The leading noisy term it gives is `(ΓL + L̄)ΛΔ/ε³`.

**This result.** The repository's [main theorem](RecursiveMomentumAffineVariance.lean) proves that
recursive momentum (unnormalized STORM, constant parameters, one initial minibatch) reaches
`E‖∇F(x_out)‖ ≤ ε` with

  `O(1 + Γ⁴ + Λ²/ε² + (L + L̄)(1 + Γ)Δ/ε² + (L + L̄)ΛΔ/ε³)`

same-sample pair calls.

**What is new.**
- Under strong growth the cost is linear in `Γ = √(ρ − 1)`. This beats SGD when `L̄ < ΓL`, and beats
  the best published variance-reduction bound by the same factor `ΓL/L̄`.
- The leading `ε⁻³` term `L̄ΛΔ/ε³` has no `Γ` factor.
- Rescaled versions of the Arjevani et al. hard instances show that, for zero-respecting algorithms,
  the class complexity is `Θ(min{(1+Γ²)L, (1+Γ)L̄}·Δ/ε²)` at `Λ = 0`. SGD attains the first branch
  and this method the second, up to the limitations listed below.
- Our search found no earlier nonconvex guarantee below SGD's `ρLΔ/ε²` under strong growth, for
  any method, and no earlier statement of the `Ω(ρLΔ/ε²)` lower bound for this class.

## Setup

[`LongTails/Setups/AffineVarianceMeanSquaredSmooth.lean`](../Setups/AffineVarianceMeanSquaredSmooth.lean)
(`LongTails.Setups.AffineVarianceMeanSquaredSmooth.spec`).

**Space.** `E` is a real complete inner-product space, Borel and second countable. This covers every
`ℝ^d` and separable Hilbert spaces.

**Objective.** `f : E → ℝ` is differentiable with an `L`-Lipschitz gradient. It is bounded below in
the form `f(x₀) − f(x) ≤ Δ` for all `x`.

**Oracle.** Samples `ξ_k` are IID with law `p`, using the repository's `IID` structure. A query
`(x, y)` returns `(g(x, ξ_k), g(y, ξ_k))`: two stochastic gradients on the same fresh sample. This is
the standard STORM/SPIDER model, the `K = 2` oracle of Arjevani et al. The map `g` is jointly
measurable, integrable and unbiased.

**Affine variance.** `∫ ‖g(x,ω) − ∇f(x)‖² dp ≤ Γ²‖∇f(x)‖² + Λ²`, with `Γ, Λ ≥ 0`. Sources:
- Bottou–Curtis–Nocedal, SIAM Review 2018, Assumption 4.3(c), in second-moment form;
- Chen–Zhou–Liang–Lu, ICML 2023, the affine-variance assumption stated before their Thm 4;
- Faw et al., COLT 2022.

`Λ = 0` is the strong growth condition (Schmidt–Le Roux 2013; Vaswani–Bach–Schmidt, AISTATS 2019).

**Mean-squared smoothness.** `∫ ‖g(x,ω) − g(y,ω)‖² dp ≤ L̄²‖x − y‖²`. This is Arjevani et al.,
eq. (4), and the STORM/SPIDER assumption. It implies `L ≤ L̄`. The constants are kept separate so
that the comparison with SGD, which only uses `L`, stays visible.

**Accuracy.** `∫ ‖∇f(x_out)‖ dP ≤ ε` over the algorithm seed and all samples.

**Cost.** Oracle calls; each call is one sample and two gradients.

All parameters `(L, L̄, Γ, Λ, Δ, ε, x₀)` are public, as in the STORM/SPIDER literature with tuned
constants. No `allowedAlgorithm` restriction is imposed.

## Algorithm and output

[`LongTails/Algorithms/RecursiveMomentum.lean`](../Algorithms/RecursiveMomentum.lean)
(`recursiveMomentum`).

1. **Initial estimate.** `d₀ = (1/B) Σ_{i<B} g(x₀, ξ_i)`, using `B` calls with query `(x₀, x₀)`.
2. **Iterations.** For `t = 0, …, T−1`:
   - `x_{t+1} = x_t − γ d_t`;
   - `d_{t+1} = g(x_{t+1}, ξ) + (1 − a)(d_t − g(x_t, ξ))`, using one pair call on a fresh `ξ`.
3. **Output.** `x_τ` with `τ` uniform on `{0, …, T}`, drawn from the algorithm's seed. The execution
   uses `B + τ ≤ B + T` calls.

**Tuning** ([`RecursiveMomentumConvergence.lean`](../Proofs/RecursiveMomentumConvergence.lean)), with
`r = 1 + 3Γ + 6Λ/ε`:
- `a = 1/(1 + 8Γ² + 32Λ²/ε²)`;
- `γ = 1/(4(L + L̄) r)`;
- `B = ⌈Γ² r + Λ²/ε²⌉ + 1`;
- `T = ⌈64(L + L̄) r Δ/ε² + 16(1 + 8Γ² + 32Λ²/ε²)⌉`.

The key choice is `a ≍ min(1/Γ², ε²/Λ²)`. Because the fresh-sample variance is relative, the momentum
only has to average over about `Γ²` samples, not `σ²/ε²`. The step is `γ ≍ √a/L̄ ≍ 1/(ΓL̄)`, where SGD
uses `1/(Γ²L)`.

## Proved guarantee

[`RecursiveMomentumAffineVariance.lean`](RecursiveMomentumAffineVariance.lean), `result`: under the
setup, `E‖∇f(x_out)‖ ≤ ε` within the budget

  `⌈16 + 131Γ² + 5Γ⁴ + 516Λ²/ε² + 64(L + L̄)(1 + 3Γ)Δ/ε² + 384(L + L̄)ΛΔ/ε³⌉ + 2`

pair calls. The budget bounds `B + T`, every call made.

## Proof idea

The proof lives in [`RecursiveMomentumMoments.lean`](../Proofs/RecursiveMomentumMoments.lean) and
[`RecursiveMomentumDescent.lean`](../Proofs/RecursiveMomentumDescent.lean). Write `e_t = d_t − ∇f(x_t)`.

1. **Error recursion.** Conditioning on the past,
   `E‖e_{t+1}‖² ≤ (1−a)²E‖e_t‖² + 2a²(Γ²E‖∇f(x_{t+1})‖² + Λ²) + 4(L̄² + L²)γ²E‖d_t‖²`.
2. **Descent.** With `γL ≤ 1/2`,
   `f(x_{t+1}) ≤ f(x_t) − (γ/2)‖∇f(x_t)‖² − (γ/4)‖d_t‖² + (γ/2)‖e_t‖²`.
3. **Lyapunov function.** Take `Φ_t = E f(x_t) + (γ/a)E‖e_t‖² − 2aγΓ²E‖∇f(x_t)‖²`. The relative-noise
   term `2a²Γ²‖∇f(x_{t+1})‖²` is charged to the *next* step's descent `−(γ/2)‖∇f‖²`, which needs
   `aΓ² ≤ 1/8`. The movement term cancels the `−(γ/4)‖d_t‖²` once `16(L̄² + L²)γ² ≤ a`.
4. **Telescoping.** The left-over `κE‖∇f(x_N)‖²` is absorbed by `‖∇f‖² ≤ 2L(f − f_low)`. This gives
   `Σ_{t≤T} E‖∇f(x_t)‖² ≤ 4Δ/γ + (4/a)E‖e₀‖² + 8aΛ²(T+1)`.
5. **Output bound.** The pointwise bound `s ≤ s²/(2ε) + ε/2` turns the averaged squared bound into
   `E‖∇f(x_out)‖ ≤ ε`.

The mechanism (step 3) is the point. Normalized variance-reduced methods (PR #15 here; Upadhyay et
al. 2026) and SPIDER-type analyses with absolute error targets cannot exploit relative noise. They pay
`ε⁻³` even at `Λ = 0` (normalized), or `Γ²` (SPIDER).

## Comparison with the closest results (same oracle and criterion up to Jensen)

| Method / source | Cost at `Λ = 0` | Leading term for `Λ > 0` | Notes |
|---|---|---|---|
| SGD, [Bottou–Curtis–Nocedal 2018](https://arxiv.org/abs/1606.04838) Thm 4.8; [Vaswani–Bach–Schmidt 2019](https://arxiv.org/abs/1810.07288) (SGC, nonconvex) | `(1 + Γ²)LΔ/ε²` | `LΛ²Δ/ε⁴` | single query per sample, no MSS needed |
| SPIDER under affine variance, [Chen–Zhou–Liang–Lu, ICML 2023](https://arxiv.org/abs/2303.02854) Thm 4 (`B ≳ max(Λ²/ε², Γ²q²)`, `B′ ≳ q`, `γ = O(ε)`) | `(1 + Γ²)L̄Δ/ε²` | `(1 + Γ)L̄ΛΔ/ε³` | `L₁ → 0` case of their class |
| Chen et al. Thm 4 on `b = Γ²` minibatched pairs (`Γ_b ≤ 1`, `Λ_b = Λ/Γ`, `L̄_b ≤ L + L̄/Γ`; our computation) | `(Γ²L + ΓL̄)Δ/ε²` | `(ΓL + L̄)ΛΔ/ε³` | never below SGD at `Λ = 0` |
| Normalized STORM under ABC (repository result `NormalizedStormExpectedSmoothness`; affine ⇒ ABC with `A = LΓ²`) | `ε⁻³`: `L̄Δ√(LΓ²Δ)/ε³` | `L̄Δ(Λ + Γ√(LΔ))/ε³` | normalized steps |
| **This result** | `(L + L̄)(1 + Γ)Δ/ε² + O(1 + Γ⁴)` | `(L + L̄)ΛΔ/ε³` | needs MSS + pair oracle |

**Improvement regimes.**
- **At `Λ = 0`:** this result beats SGD and every published variance-reduction bound when `L̄ ≪ ΓL`,
  by a factor of order `ΓL/L̄`. This requires `ε² ≲ L̄Δ/Γ³`, so that the `ε`-free `Γ⁴` term is
  dominated.
- **For `Λ > 0`:** the leading `ε⁻³` coefficient improves on minibatched Chen et al. by
  `(ΓL + L̄)/L̄`. It improves on SGD's `ε⁻⁴` whenever `ε ≲ LΛ/L̄`.
- **When `L̄ ≳ ΓL`:** there is no gain. SGD, or minibatched SPIDER, is as good up to constants.

## Lower bounds (hand-checked sketches, not formalized)

All of the following concern **zero-respecting** algorithms. They come from the constructions of
[Arjevani et al., *Lower bounds for non-convex stochastic optimization*](https://arxiv.org/abs/1912.02365),
v2 (Math. Program. 2023), §3, with constants `Δ₀`, `ℓ₁ = 152`, `ℓ̄₁ = 328` and `ς = 23`.

1. **Both hard oracles satisfy strong growth.** The oracle `g_T` of eq. (17) (Lemma 3) and the
   smoothed oracle `ḡ_T` of eq. (20) (Lemma 4) have error supported on one coordinate. That
   coordinate is `prog_{1/4}(x)+1` for `g_T` and `prog_{1/2}(x)+1` for `ḡ_T`, and the error equals
   `∇_iF_T(x)·Θ_i(x)(z/p − 1)` with `Θ_i ∈ [0,1]`. Hence `E‖error‖² ≤ ((1−p)/p)‖∇F_T(x)‖²`, i.e.
   affine variance with `Λ = 0` and `Γ² = (1−p)/p`. This ratio is invariant under the rescaling used
   in their Theorems 1–2.
2. **Without MSS, any number of queries per sample.** Theorem 1's scaling with `p = 1/(1+Γ²)` gives
   `Ω((1 + Γ²)LΔ/ε²)` for `ε ≲ √(LΔ)`. So SGD is optimal for the strong-growth class without MSS.
   Note that affine variance plus MSS together are needed for any gain.
3. **With MSS.** Take `ḡ_T` with instance smoothness `L_i ≤ L`. Rescaling gives MSS constant
   `L̄ = (ℓ̄₁/ℓ₁)L_i/√p` and `(T−1)/(2p) ≍ L_iΔ/(pε²)` queries. Maximizing over `L_i` and
   `p ≥ 1/(1+Γ²)` gives `Ω(min{(1 + Γ²)L, (1 + Γ)L̄}·Δ/ε²)`. In the MSS branch this needs
   `ε² ≲ L̄Δ/Γ`.
4. **With `Λ > 0`.** Arjevani et al. Theorem 2 with `Γ = 0` and `σ = Λ` gives `Ω(L̄ΛΔ/ε³ + Λ²/ε²)`.

**Scope of the lower bounds.**
- **Randomized algorithms.** The extension in their §4 adds `ηx` and `J(x)ᵀU` terms. Strong growth
  there would need a large-gradient lemma for the randomized instance, which we did not check. So
  the lower bounds are claimed for zero-respecting algorithms only.
- **No separation between SGD and this method.** In the MSS branch the hard instances have
  `L_i ≍ L̄/Γ`, where SGD also costs about `ΓL̄Δ/ε²`. They show optimality on the class; they do not
  show that SGD itself is slower on a specific nonconvex instance.

## When is `L̄ ≪ ΓL`? Evidence that the constants separate

**Realizable least squares.** Take `F(x) = E_a ½⟨a, x − x*⟩²` with `‖a‖ ≤ R` and `H = E aaᵀ`.
- Smoothness and MSS: `L = λ_max(H)`, and `L̄² ≤ R²L`, since `E⟨a,Δ⟩²‖a‖² ≤ R²ΔᵀHΔ`.
- Strong growth on `range(H)`: `Γ² ≤ R²/λ⁺_min(H)`.
- Hence `ΓL/L̄ ≥ √(L/λ⁺_min) = √κ`.

**A spiked instance.** Take `a_i = √c·u + √(1−c)·v_i` with orthonormal `u, v₁, …, v_n`. Then
`L ≈ L̄² ≈ c` and `Γ² ≈ n/(1−c)`, so SGD costs `≈ cnΔ/((1−c)ε²)` while this method costs
`≈ √(cn/(1−c))·Δ/ε²`.

**Caveats.**
- These instances are **convex**. On them, other methods are better still:
  - SGD converges linearly at `Λ = 0`;
  - accelerated SGD under strong growth improves further
    ([Valls–Wang 2022](https://arxiv.org/abs/2207.11833),
    [Mishkin–Pilanci et al. 2024](https://arxiv.org/abs/2404.02378));
  - with label noise, averaged constant-step SGD needs only `O(ε⁻²)`.
  They only show that the regime `L̄ ≪ ΓL` is not vacuous.
- **Nonlinear models.** For realizable nonlinear least squares, the per-sample Hessian is dominated by
  the Gauss–Newton term near interpolation. A heuristic version of the computation gives
  `ΓL/L̄ ≈ √κ(E J_aᵀJ_a)`, which involves large NTK/Gauss–Newton condition numbers. Spurious critical
  points force `Λ > 0`. We have no explicit nonconvex, non-PL family with proven constants.

**Framing.** The contribution is therefore a class-level statement on Chen et al.'s class: nonconvex,
`L`-smooth, affine variance plus MSS, and the same-sample oracle.

## Limitations

- **The `ε`-free `Γ⁴` term.** It comes from the initial batch `B ≍ Γ²r`, which includes `Γ³` and
  `Γ²Λ/ε`; the budget bounds these by `Γ²`, `Γ⁴` and `Λ²/ε²`. Upper and lower bounds therefore match
  only once `(1+Γ)L̄Δ/ε²` dominates `Γ⁴`, i.e. for `ε² ≲ L̄Δ/Γ³`. Removing it, for example with a
  time-varying momentum warm-up, is open.
- **The noiseless term.** It is `(L + L̄)Δ/ε²`, not `LΔ/ε²`.
- **Known parameters.** The tuning uses `L, L̄, Γ, Λ, Δ, ε`; no adaptivity is claimed.
- **Oracle.** The same-sample pair oracle costs two gradients per call. Without it (lower bound 2),
  SGD is optimal.
- **Criterion.** Expected stationarity at a uniformly random iterate. No high-probability or
  last-iterate statement is made.
- **Novelty search.** Our search found no nonconvex variance-reduction or other guarantee that is
  linear in `Γ` under strong growth or affine variance. We searched arXiv, ICML/ICLR/NeurIPS 2024–2026
  and the general web for STORM, SPIDER, SARAH, PAGE, Hybrid-SGD, META-STORM and adaptive variance
  reduction under strong growth, interpolation or affine/relaxed variance. We read Chen et al. Thm 4
  in full, and Li–Richtárik 2020, Khaled–Richtárik 2023, PAGE, Jiang et al. 2024, META-STORM and
  Upadhyay et al. 2026 at the assumption level. We did not check the Tyurin–Richtárik DASHA/MARINA
  frameworks in full. The lower-bound observation that Arjevani's oracles satisfy strong growth does
  not appear in their v2.
