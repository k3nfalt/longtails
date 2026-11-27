# Two-oracle stochastic sliding for nonconvex composite problems: upper bound

Lean: [`SlidingStochasticCompositeUpperBound.lean`](SlidingStochasticCompositeUpperBound.lean),
setup [`SlidingStochasticComposite.lean`](../Setups/SlidingStochasticComposite.lean),
algorithm [`Algorithms/SlidingStochasticComposite.lean`](../Algorithms/SlidingStochasticComposite.lean).
The matching lower bound is
[`SlidingStochasticCompositeLowerBound.lean`](SlidingStochasticCompositeLowerBound.lean); see
[its note](SlidingStochasticCompositeLowerBound.md).

## Problem and oracles

We minimize `F = f + h` over a finite-dimensional Euclidean space, where:

- `f` is differentiable with an `ℓ`-Lipschitz gradient and may be nonconvex;
- `h` is convex and differentiable with an `L`-Lipschitz gradient (no prox of `h` is assumed);
- `F(x0) - inf F ≤ Δ`.

The oracle model is gradient-only (no function values and no proximal maps). There are two oracles, counted
separately:

- oracle `0` returns the exact gradient `∇f(x)`;
- oracle `1` returns `g(x, ξ)`, where the samples `ξ_t` are IID, `E g(x, ξ) = ∇h(x)` and
  `E ‖g(x, ξ) - ∇h(x)‖² ≤ σ²`. The oracle must be jointly measurable.

The setup does not fix the algorithm (`allowedAlgorithm` is not used).

**Accuracy criterion.** We use the Moreau gap at the weak-convexity scale `ℓ`:

    Γ(x) = F(x) - inf_y { F(y) + ℓ ‖y - x‖² },   success: E Γ(x̂) ≤ ε² / (8ℓ).

`F` is `ℓ`-weakly convex, so `Γ ≥ 0`. The criterion relates to standard ones as follows:

- `‖∇F(x)‖ ≤ ε/2` implies `Γ(x) ≤ ε²/(8ℓ)`. So this target is implied by the usual gradient-norm target up to a constant
  factor, and the lower bound proved for it is the stronger statement.
- Conversely, `Γ(x) ≤ ε²/(8ℓ)` gives `‖∇F_{1/(2ℓ)}(x)‖ ≤ ε`, where `F_{1/(2ℓ)}` is the Moreau envelope. By Jensen this
  holds in expectation as well. The prox point `y⁺(x)` is within `ε/(2ℓ)` of `x` and is an ε-stationary point.
  This is the standard criterion for weakly convex problems; see
  [Davis–Drusvyatskiy 2019, §2](https://arxiv.org/abs/1803.06523).
- Extracting an explicit ε-stationary point from `x̂` needs one `ℓ`-strongly convex prox subproblem. We expect it to cost
  `O(log)` ∇f calls and `O((√(L/ℓ) + σ²/ε²) log)` ∇h calls with the same prox-linear/AC-SA machinery and restarts.
  This is a sketch only: it is neither proved here nor formalized.

## Algorithm

Prox-linear sliding (`method` in the algorithm file). The method runs `M` stages. Stage `k` has center `c_k` and uses:

- one exact call `∇f(c_k)`;
- `N` stochastic ∇h calls in the repository's accelerated stochastic approximation (AC-SA) scheme
  (`Gradient.acceleratedRun`, with `D = ℓN(N+1)/8`). The scheme is applied to the `ℓ`-strongly convex model

      Q_k(y) = f(c_k) + ⟨∇f(c_k), y - c_k⟩ + h(y) + (ℓ/2) ‖y - c_k‖².

The next center is the inner output. The returned point is the center of a uniformly random stage, drawn from the
algorithm's seed.

## Guarantee (Lean `result`)

With `M = ⌈32 ℓΔ/ε²⌉₊ + 1` and `N = ⌈4√(1 + L/ℓ) + 256 σ²/ε²⌉₊`, the method succeeds with the budget

    ∇f calls:  M
    ∇h calls:  M · N  =  O( ℓΔσ²/ε⁴ + √(ℓL) Δ/ε² + ℓΔ/ε² + √(1 + L/ℓ) + σ²/ε² ).

The proof works per stage:

- `Γ(c_k) ≤ G_k := F(c_k) - min Q_k`.
- Strong convexity gives `‖c_k - y_k*‖² ≤ 2G_k/ℓ`.
- The repository's AC-SA bound then gives `E[F(c_{k+1})] ≤ F(c_k) - G_k/2 + 8σ²/(ℓ(N+1))`.
- Telescoping over the `M` stages, and averaging over the random output index, gives `E Γ ≤ ε²/(8ℓ)`.

Measurability and integrability of `Γ ∘ output` are proved, and every oracle call made by the execution is counted.

## What is new and what is known

- **Stated guarantee.** As far as we found, this is the first stated two-oracle guarantee for this class: nonconvex
  smooth `f` with exact gradients plus convex smooth `h` with stochastic gradients, with `∇f` and `∇h` counted
  separately. We make no claim of technical novelty for the upper bound. It composes standard pieces: a prox-linear
  outer loop and accelerated stochastic approximation on a strongly convex model.
- **Convex case.** Gradient sliding is classical for convex problems:
  - [Lan 2016](https://arxiv.org/abs/1406.0919), GS/SGS;
  - [Lan–Ouyang](https://arxiv.org/abs/1609.04905), accelerated gradient sliding;
  - [Kovalev et al., NeurIPS 2022](https://arxiv.org/abs/2205.15136), optimal gradient sliding. This requires a convex
    total objective.
- **Nonconvex single-oracle work.**
  - [Ghadimi–Lan 2016](https://arxiv.org/abs/1310.3787) treats a stochastic nonconvex part plus a *simple* convex part.
    That is the reverse placement of the noise, with one oracle.
  - [Lan–Li–Xu, arXiv:2412.14291v3](https://arxiv.org/abs/2412.14291) study separate upper and lower curvatures with a
    single oracle.
  - For a single oracle on `ℓ`-weakly convex, `L`-smooth `F`, inexact proximal-point and Catalyst-type schemes give
    `O(√(ℓL)Δ/ε²)` up to logarithms. These include Kong–Melo–Monteiro (cited in Lan–Li–Xu) and
    [Carmon et al. 2018](https://arxiv.org/abs/1611.00756). Allen-Zhu's SGD4 ([1801.02982](https://arxiv.org/abs/1801.02982))
    covers the stochastic single-oracle case. When `∇f` and `∇h` are always queried together, our bound gives the
    single-oracle count `O((1 + ℓΔ/ε²)(√(1 + L/ℓ) + σ²/ε²))`, which contains `ℓΔσ²/ε⁴ + √(ℓL)Δ/ε²` and has no
    logarithms.
- **Practical message.**
  - The expensive nonconvex gradient is called only `O(ℓΔ/ε²)` times, the gradient-descent count for `f` alone.
    This count is independent of `L` and `σ`.
  - All dependence on the conditioning of `h` (`√(L/ℓ)` per stage) and on the noise (`σ²/ε²` per stage) is moved to the
    cheap oracle.
- **Tightness.** The paired lower bound shows that both counts are optimal up to universal constants on its valid
  regime (`ℓΔ ≥ 2⁶²ε²` and a high-dimension condition). This holds for every randomized algorithm, and each count holds
  no matter how many calls the other oracle receives.

## Example

A gradient-step-denoiser plug-and-play prior plays the role of `f`:

- `f = λ g_θ` is a learned potential with Lipschitz gradient that is nonconvex
  ([Hurault–Leclaire–Papadakis, ICLR 2022](https://arxiv.org/abs/2110.03220)).
- Each `∇f` call is one network backpropagation, and `ℓ = λ·Lip(∇g_θ)`.

A streaming data term plays the role of `h`. The noise must be bounded independently of `x`:

- **Fixed operator.** `h(x) = E_ζ ½‖A x - b_ζ‖²` with a fixed forward operator `A` and noisy measurements
  `b_ζ = A x♮ + ζ`. It is convex with `L = ‖A‖²`. The stochastic gradient `Aᵀ(Ax - b_ζ)` has noise `-Aᵀζ`, so
  `σ² = E‖Aᵀζ‖²` does not depend on `x`.
- **Robust losses.** `h(x) = E_ζ ψ(⟨a_ζ, x⟩ - b_ζ)` with a Huber-type `ψ` (`|ψ'| ≤ 1`, `0 ≤ ψ'' ≤ 1`), with rows
  `a_ζ` sampled online. This gives `L ≤ E‖a_ζ‖²` and `σ² ≤ E‖a_ζ‖²`, uniformly in `x`. Least squares with sampled
  rows (as in online plug-and-play, [Sun–Wohlberg–Kamilov, IEEE TCI 2019](https://arxiv.org/abs/1809.04693)) does
  **not** satisfy the uniform-variance assumption, because its noise grows with `‖x‖`.
- In either case `h` has no cheap prox in general.

`F` is a genuinely interacting nonlinear function. The result asks for at most `ℓΔ/ε²` network gradients, and for
`O((ℓΔ/ε²)(√(L/ℓ) + σ²/ε²))` cheap data gradients.

## Limitations

- The criterion is the Moreau gap; see above for the relation to gradient-norm accuracy.
- Matching with the lower bound is claimed only on the lower bound's valid regime. Outside it, the additive lower-order
  terms of this budget are not shown to be necessary.
- The `σ²/ε²` and `√(1 + L/ℓ)` terms are additive, so the budget is not reduced in benign regimes such as `σ = 0` with
  `L ≈ ℓ`. Constants have not been optimized.
- The guarantee is in expectation. No high-probability version is proved.
- The noise model is bounded variance with IID samples.
