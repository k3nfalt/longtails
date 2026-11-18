# Tight complexity of nonconvex stochastic optimization under expected-smoothness (ABC) noise — lower bound

Lean theorem: [`AbcNoiseLowerBound.lean`](AbcNoiseLowerBound.lean) (`result : NonConvergence spec budget`).
Setup: [`../Setups/HighDimensionalAbcNoiseNonconvex.lean`](../Setups/HighDimensionalAbcNoiseNonconvex.lean), a parameter restriction of the general setup [`../Setups/AbcNoiseNonconvex.lean`](../Setups/AbcNoiseNonconvex.lean), with the formal inclusion [`../Proofs/AbcNoiseInclusion.lean`](../Proofs/AbcNoiseInclusion.lean).
Hard instance: [`AbcChain*`](../Proofs/AbcChain.lean), [`AbcHardFunction`](../Proofs/AbcHardFunction.lean), [`AbcHardGeometry`](../Proofs/AbcHardGeometry.lean), [`AbcHardOracle`](../Proofs/AbcHardOracle.lean); hiding and coupling: [`AbcHardSimulation`](../Proofs/AbcHardSimulation.lean), [`AbcHardExecution`](../Proofs/AbcHardExecution.lean), [`AbcHardCounting`](../Proofs/AbcHardCounting.lean); probability and assembly: [`AbcLowerMeasure`](../Proofs/AbcLowerMeasure.lean), [`AbcLowerParameters`](../Proofs/AbcLowerParameters.lean), [`AbcLowerAssembly`](../Proofs/AbcLowerAssembly.lean), [`AbcLowerBound`](../Proofs/AbcLowerBound.lean).
Matching upper bound: [`AbcNoiseSgdUpperBound.lean`](AbcNoiseSgdUpperBound.lean) and its note.

## Problem class (Khaled–Richtárik expected smoothness)

Minimize a differentiable `f : E → ℝ` with `L`-Lipschitz gradient, bounded below with infimum `f⋆ = inf f` (stated as `f⋆ ≤ f` everywhere and `∀η>0 ∃x, f x < f⋆+η`), and `f(x₀) − f⋆ ≤ Δ`.
Each oracle call at a query `x` draws a fresh sample `ω` from an IID stream (abstract law `P` with the repository `IID` structure) and returns `g(x, ω)`, jointly measurable, integrable, unbiased, and with

```
E_ω ‖g(x,ω) − ∇f(x)‖² ≤ 2A (f(x) − f⋆) + B ‖∇f(x)‖² + C        for every x.
```

This is the ABC (expected smoothness) condition of Khaled & Richtárik, *Better Theory for SGD in the Nonconvex World*, TMLR 2023 ([arXiv 2002.03329v3](https://arxiv.org/abs/2002.03329), Assumption 2), building on the expected-smoothness framework of Gower et al., *SGD: General Analysis and Improved Rates*, ICML 2019 ([arXiv 1901.09401](https://arxiv.org/abs/1901.09401)). It is written here in variance form. Their second-moment form with constants `(A, B_KR, C)` implies this one with `B = max(B_KR − 1, 0)`, since `E‖g‖² = ‖∇f‖² + variance`; their interpolation examples with `B_KR < 1` fall under `B = 0`. No complexity term changes. It contains bounded variance (`A = B = 0`, `C = σ²`), relative/affine variance (`A = 0`), and noise that scales with the suboptimality (`B = C = 0`, the variance analogue of the weak growth condition of Vaswani–Bach–Schmidt, AISTATS 2019). The offset is the true infimum `f⋆ = inf f`, as in Khaled–Richtárik; see "Why the infimum matters" below.

Accuracy criterion: the returned point `x̂` satisfies `E‖∇f(x̂)‖ ≤ ε` (the expectation is over the product of the algorithm's internal randomness and the oracle law, as fixed by `LongTails/Template.lean`).

The lower-bound setup fixes `E = ℝ^d` (`EuclideanSpace ℝ (Fin d)`) and the sample space `Ω = ℝ`, and adds the regime conditions

```
2^26 ε² ≤ L Δ,      2^40 (1 + LΔ(1 + B + AΔ/ε² + C/ε²)/ε²)^4 ≤ d.
```

The first is the usual "nontrivial accuracy" condition (it only excludes ε comparable to √(LΔ)); the second is a polynomial dimension requirement, standard for lower bounds against arbitrary randomized algorithms (as in the repository's randomized smooth convex lower bound). The general setup has no such restriction, and `AbcNoiseInclusion` proves that the restricted setup is included in the general one, so the upper bound applies to every instance used here. The regime is nonempty for all `A, B, C ≥ 0`, including `A > 0, B = C = 0`.

## Result

For every valid parameter tuple, every randomized adaptive algorithm (no zero-respecting or span assumption, no restriction on its internal randomness or output rule) and every call budget `b ≤ budget` (including `b = 0`), there is an admissible instance and oracle on which `E‖∇f(x̂)‖ > ε` (or the output fails measurability/integrability), where

```
budget = ⌊ L Δ (1 + B + A Δ/ε² + C/ε²) / (2^53 ε²) ⌋.
```

In order notation, every algorithm needs

```
Ω( L Δ/ε² + B · L Δ/ε² + L A Δ²/ε⁴ + L Δ C/ε⁴ )
```

oracle calls. Together with the upper bound (`AbcNoiseSgdUpperBound`: plain SGD with a uniformly sampled iterate, `⌈144 LΔ(1 + B + AΔ/ε² + C/ε²)/ε²⌉ + 1` calls, which is Khaled–Richtárik's Corollary 1 rate), the complexity of the class is

```
Θ( (L Δ/ε²) · (1 + B + A Δ/ε² + C/ε²) )
```

up to universal constants (no logarithms), in the regime above. The constant gap `144 · 2^53` is universal and not optimized.

## What is new and what is known

* **Known pieces.** The `C`-term `Ω(LΔC/ε⁴)` for every randomized algorithm is Arjevani et al., *Lower bounds for non-convex stochastic optimization*, Math. Program. 2023 ([arXiv 1912.02365](https://arxiv.org/abs/1912.02365), Theorem 3). The deterministic term `Ω(LΔ/ε²)` is Carmon et al., Math. Program. 2020. The `B`-term `Ω(B·LΔ/ε²)` follows from the standard Bernoulli-masking reduction for relative noise; it is included only to state the complete four-term bound and is not claimed as new. All these terms are proved here from scratch in one hard family.
* **New: the `A`-term `Ω(L A Δ²/ε⁴)`**, valid for every randomized algorithm. We found no lower bound in the `A` coefficient for nonconvex ABC / expected-smoothness / weak-growth noise in the literature (searches up to 2026-11).
  * The closest works, Fazla et al. [arXiv 2604.16620](https://arxiv.org/abs/2604.16620) and Upadhyay et al. [arXiv 2605.15314](https://arxiv.org/abs/2605.15314), concern the different distance-based Blum–Gladyshev model.
  * Kawamoto–Iiduka [arXiv 2510.20608](https://arxiv.org/abs/2510.20608) gives only upper bounds for SGD under expected smoothness.
  * The repository's [`NormalizedStormExpectedSmoothness`](NormalizedStormExpectedSmoothness.md) note records the missing `A`-lower bound. The consequence is that Khaled–Richtárik-tuned SGD is minimax optimal, up to universal constants, simultaneously in `L, Δ, ε, A, B, C`, and that noise which shrinks with the suboptimality gap does not help in the worst case: any method pays as if the variance were of order `AΔ` during the first half of the run. In particular `A > 0` with `B = C = 0` already forces `ε⁻⁴` dependence for every algorithm, in contrast with `A = 0` (strong-growth-type noise), where `ε⁻²` is achievable. (This statement is about the ABC oracle model; we do not claim it for finite sums whose stochastic gradients are gradients of nonnegative component functions.)

### Why the infimum matters

If the assumption allowed any lower bound `f_low ≤ inf f` in place of `inf f` (as the repository's MSS setup `ExpectedSmoothnessNonconvex` does), the `A`-term would be a two-line corollary of Arjevani et al.: take their bounded-variance instance with gap `Δ/2` and variance `σ² = AΔ` and set `f_low = inf f − Δ/2`. With the original definition `f⋆ = inf f`, the noise budget `2A(f − f⋆)` must vanish near every approximate minimizer, so a constant-variance oracle is no longer admissible and the statement of Arjevani et al.'s theorem cannot be reused; only their technique is.

## Hard instance and proof

1. **Chain.** On `ℝ^T` (`T = n+1`), `F(u) = −Φ(u₁) + Σ_{i<T} [Ψ(−u_i)Φ(−u_{i+1}) − Ψ(u_i)Φ(u_{i+1})]`, Carmon et al.'s chain with `C^{1,1}` piecewise-polynomial profiles: `Ψ = 16(r(t−½) − 2r(t−¾) + r(t−1))` and `Φ = r(t+2) − r(t+1) − r(t−1) + r(t−2)`, where `r(s) = (s₊)²/2`. Proved facts: every partial derivative is nonpositive; `|u_T| < 1 ⇒ ∃k, ∂_kF ≤ −1`; `∇F` is 1000-Lipschitz with a quadratic model; `−3T ≤ F ≤ 3T`, `inf F = −3T`; and if all coordinates from index `m` on are at most `1/4` then `F(u) − inf F ≥ 3(T − m − 1)` (gap lemma).
2. **Hiding and wall.** A hidden embedding `π : Fin T ↪ Fin d`, the chain evaluated on the coordinates `w_{π(i)}`, glued by the repository's `smoothMax` to the π-independent wall `(‖w‖² − R²)/R` (`R = 2048T`, width `256T`). The function equals the chain near the origin and the wall outside radius `2R`. At every point whose chain is unfinished (`|u_T| < 1`) the gradient has norm at least `1/20`, including the gluing region (radial argument using `⟨∇F(u), u⟩ ≥ −54T`). The scaled objective `f = a·H((x − x₀)/λ)` with `a/λ = 60ε` and `1024a/λ² = L` is `L`-smooth with gap at most `3aT ≤ Δ`.
3. **Masked oracle.** Masking only the gradient component along the next hidden coordinate, as in Arjevani et al.'s zero-respecting construction, is not enough against randomized algorithms under coordinate hiding. The visible `m`-th component then contains `Ψ'(±u_m)Φ(±u_{m+1})`, which depends on the value of the query at the hidden position `π(m+1)`. A query whose unrevealed coordinates carry distinct small values would identify `π(m+1)` in one call without any coin success. The construction therefore masks the whole next link: with `m = stage(x)` (one plus the largest index of a chain coordinate above `1/4`), the reply is `known_m(x) + coin(q_m, ω)·secret_m(x)`, where `coin(q, ω) = 1[ω ≤ q]/q`, `ω ~ Unif[0,1]`. The known part is the gradient of the objective with the chain truncated at `m` and the **whole next link masked**, including the `Ψ'(u_m)Φ(u_{m+1})` part of the `m`-th coordinate; it depends on `π` only through `π(<m)`. The secret has norm at most `1740ε`. The reveal probability is `q_m = c/max(c, b_m)`, with `c = (1740ε)²` and `b_m = 6Aa(n − m) + 9Bε² + C`. By the gap lemma and the gradient lower bound, `b_m` is at most the ABC budget at every point of stage `m`, so the variance is at most `b_m`. The reply is unbiased and jointly Borel.
4. **Counting.** For fixed algorithm seed and oracle seeds, a simulated execution that knows only the prefix `π(< c_t)`, where `c_t` counts the steps `s < t` with `ω_s ≤ q̄`, coincides with the true execution unless some query or the output has a large coordinate at an unrevealed position. Here `q̄` is the reveal probability at half the chain. The repository's prefix-family counting (`bounded_prefix_bad_count`) bounds the fraction of such embeddings by `1/8`. The expected count is `E c_N = N q̄`, using only the IID marginals, so for `N ≤ budget` Markov gives `P(c_N > n/2) ≤ 1/8`. On the remaining event the output stays below stage `T`, so `‖∇f(x̂)‖ ≥ 3ε`. Averaging over embeddings yields one embedding with `E‖∇f(x̂)‖ ≥ 3ε·(7/8)² > ε`. The hard instance depends on the algorithm but not on its realized seed.
5. **Budget.** The bound `q̄ ≲ ε²/(AΔ + Bε² + C + ε²)` and `T ≍ LΔ/ε²` give `T/(16 q̄) ≥ budget`, which is proved in `AbcLowerParameters.budget_reveal`.

## How the result meets the strict research direction

* *Important and popular setup.* The ABC / expected-smoothness noise model of Gower et al. (ICML 2019) and Khaled–Richtárik (TMLR 2023) is the standard general noise assumption for SGD analyses: it contains bounded variance, affine variance and gap-dependent noise. The problem is smooth nonconvex optimization with stochastic first-order oracles.
* *Almost tight upper and lower bounds, both in the repository.* The upper bound is [`AbcNoiseSgdUpperBound.lean`](AbcNoiseSgdUpperBound.lean). It formalizes Khaled–Richtárik's SGD rate in this setup and is not new. The lower bound is this theorem. Together they give `Θ((LΔ/ε²)(1 + B + AΔ/ε² + C/ε²))` up to a universal constant factor (`144·2^53` between the two budgets), with no logarithmic factors, for every parameter tuple in the regime `2^26 ε² ≤ LΔ` with polynomially large dimension, including `A > 0, B = C = 0`.
* *Reuse of techniques.* The hidden-chain technique of Carmon et al. and the reveal coins of Arjevani et al. are reused. The new ingredients are the stage-dependent reveal probability driven by the gap lemma, which is needed because of `f⋆ = inf f`, and the whole-link masking needed against randomized algorithms.
* *Closing a problem.* The worst-case oracle complexity of the ABC class is settled up to constants. In particular the optimal dependence on the `A` coefficient was open.

## Limitations

* The constants are universal but huge, and the dimension must be polynomially large in the bound (standard for lower bounds against arbitrary randomized algorithms; no fixed-dimension claim).
* The result is in expectation (`E‖∇f(x̂)‖ ≤ ε`); no high-probability or `log(1/δ)` term is claimed.
* It concerns the ABC oracle model. Mean-squared-smooth (variance-reduced) ABC oracles, which give the different rate `LΔ√(AΔ+C)/ε³` of the repository's STORM result, are not covered, and nothing is claimed for interpolating finite sums.
* Literature coverage: arXiv and conference proceedings through 2026-11-14 (searches for ABC, expected smoothness, weak growth, affine and relative variance, interpolation lower bounds); OpenReview submissions not mirrored on arXiv could not be checked.
