# Biased SGD is minimax optimal: relative bias costs 1/(1−m) and 1/(1−m)², up to constants (lower bound)

Lean files:
- [theorem](BiasedNoiseLowerBound.lean)
- setups: [lower-bound regime](../Setups/HighDimensionalBiasedNoiseNonconvex.lean) and [general class](../Setups/BiasedNoiseNonconvex.lean), with the [formal inclusion](../Proofs/BiasedNoiseInclusion.lean)
- hard instance: [decoy profile](../Proofs/BiasedDecoy.lean), [lifting maps and parameters](../Proofs/BiasedLowerInstance.lean), [objective and switching oracle](../Proofs/BiasedLowerOracle.lean), [admissibility](../Proofs/BiasedLowerAdmissible.lean), [execution and averaging](../Proofs/BiasedLowerBound.lean)
- companion upper bound: [BiasedNoiseSgdUpperBound](BiasedNoiseSgdUpperBound.md)

## Problem class: SGD with biased gradients (Ajalloeian–Stich)

Minimize a differentiable `f : E → ℝ` with the following properties:
- the gradient is `L`-Lipschitz;
- `f` is bounded below, and `f⋆ = inf f` need not be attained;
- `f(x₀) − f⋆ ≤ Δ`.

Each oracle call at a query `x` draws a fresh IID sample `ω` and returns `g(x, ω)`. Write `μ(x) = E_ω g(x, ω)` for the mean of the estimator. The class allows a **bias** `b(x) = μ(x) − ∇f(x)` and **noise** `n = g − μ` with

```
‖μ(x) − ∇f(x)‖² ≤ m ‖∇f(x)‖² + ζ²,      0 ≤ m < 1,                 ((m, ζ²)-bounded bias)
E_ω ‖g(x, ω) − μ(x)‖² ≤ M ‖μ(x)‖² + σ²,                             ((M, σ²)-bounded noise)
```

for every `x`. These are Assumptions 4 and 3 of Ajalloeian and Stich, *On the Convergence of SGD with Biased Gradients* ([arXiv:2008.00051](https://arxiv.org/abs/2008.00051), v2, ICML 2020 workshop). The pair is the "bias–noise decomposition" (BND, Assumption 6) of Demidovich et al., *A Guide Through the Zoo of Biased SGD* ([NeurIPS 2023, arXiv:2305.16296](https://arxiv.org/abs/2305.16296)). Both conditions are copied verbatim. In particular, the noise bound is relative to the mean `∇f + b`, as in the source.

- The oracle is gradient-only, as in both papers.
- The criterion is `E‖∇f(x̂)‖ ≤ ε` under the joint law of the algorithm and oracle.
- `valid` contains the error-floor condition `16ζ² ≤ (1 − m)ε²`. Ajalloeian–Stich prove the floor `ζ²/(1−m)` unavoidable (their Remark 5), so accuracies below it are excluded on purpose.

Write `r := (1 − m)ε²` for the effective squared accuracy.

## Result

`result : NonConvergence spec budget` with

```
budget = ⌊ L Δ (1 + M + σ²/r) / (2^60 r) ⌋,       r = (1 − m) ε².
```

Fix any randomized algorithm, with any internal randomness, adaptive queries and output rule, and any call count `b ≤ budget`, including `b = 0`. Then there is an admissible objective and oracle on which `E‖∇f(x̂)‖ > ε`. The instance depends on the algorithm and on `b`, but not on the realized seeds.

The [lower-bound setup](../Setups/HighDimensionalBiasedNoiseNonconvex.lean) works in `E = ℝ^{d+1}` with `Ω = ℝ`. It adds two conditions to `valid`:

```
2^28 ε² ≤ L Δ,        2^40 (1 + L Δ (1 + M + σ²/r)/r)^4 ≤ d.
```

The first is the usual nontrivial-accuracy condition. The second is a polynomial dimension requirement inherited from the repository's randomized chain. Its admissibility and success predicates are literally those of the general class ([inclusion](../Proofs/BiasedNoiseInclusion.lean)), so the companion upper bound applies to every hard instance. The regime is nonempty for every `m ∈ [0,1)`, `M, σ, ζ` obeying the floor, and `d` large.

**Tightness.** Plain constant-step SGD with a uniformly random output ([upper theorem](BiasedNoiseSgdUpperBound.lean)) uses

```
⌈16 L Δ (1 + M + σ²/r) / r⌉ + 1
```

calls on the general class. Since `x ≤ ⌊x⌋ + 1`, on the valid set the upper budget is at most `2^64 · (budget + 1) + 2`. So the class complexity is

```
Θ( (L Δ / ((1 − m) ε²)) · (1 + M + σ² / ((1 − m) ε²)) )
```

up to universal constants, with no logarithms, uniformly in `m ∈ [0, 1)`.

## What is new

The upper bound is known: it is Ajalloeian–Stich, Theorem 4, in our normalisation. Their text observes that bias "increases [the iteration count] by a factor of (1−m) in the deterministic case, or by (1−m)² if the noise term is dominating". It does not show that this is necessary; the only tightness statement there is the ζ-floor (Remark 5).

The new mathematical statement is the lower bound. It holds for every randomized gradient-only algorithm.
- The deterministic term needs a factor `1/(1−m)`. At `σ = M = 0` this gives the nonconvex complexity `Θ(LΔ/((1−α²)ε²))` of the classical relative-error gradient model `‖g − ∇f‖ ≤ α‖∇f‖` with `α² = m` (B. T. Polyak, *Introduction to Optimization*, Optimization Software, 1987, Ch. 4, on gradient methods with relative errors), attained by plain gradient descent with step `1/L`. Both directions also hold for history-dependent errors: the lower bound uses only an `x`-dependent bias, and the descent argument for GD with step `1/L` uses the relative-error inequality at each iterate only.
- The noise term needs `1/(1−m)²`. Relative bias therefore hurts noisy problems quadratically more than noiseless ones, and no method can mitigate this in this oracle model: momentum, variance reduction with single-point queries, normalisation, adaptive steps, or cleverer output rules are all covered.
- The `M`-term `(1+M)/(1−m)` is also necessary.

Demidovich et al. (§1, contribution list) write that they "recover the optimal rates for general smooth nonconvex problems and for problems under the PŁ condition in the unbiased case and prove that these rates are also optimal in the biased case". We found no lower-bound construction or citation behind the biased claim for `m > 0`. The present theorem supplies one for nonconvex stationarity in the BND class.

## Construction: a decoy slope hidden in the bias budget

1. **Base chain.** Take the repository's randomized ABC hard instance `(F, O_F)` on `ℝ^d` ([AbcNoiseLowerBound](AbcNoiseLowerBound.md)). Use smoothness `L/2`, gap `Δ/2`, `A = 0`, `B = M`, `C = σ²` and accuracy scale `ε_a = 4ε/(3 max(κ, 4/3))`, where `κ² = m/(1−m)`. On the good event of that proof (few coins, no coordinate guessed) every query **and** the output satisfy `‖∇F‖ ≥ θ := 3ε_a` ([`good_query_gradient`](../Proofs/BiasedLowerBound.lean), a pointwise extension of the repository's `good_gradient`).

2. **Decoy.** Add one coordinate `z` with a random sign `s ∈ {±1}` and set

   ```
   f(x, z) = F(x) + κθ · p(s·z − c),     p(t) = √(t² + w²),   c = 100w,   w = 2(κθ + ε)/L.
   ```

   The decoy is separable, `(L/2)`-smooth, and increases the gap by at most `100κθw ≤ Δ/2`. Its slope satisfies `|p′| ≤ 1`. It is at least `0.99` at one of `±z` for every `z` ([`sign_sum_ge`](../Proofs/BiasedDecoy.lean)).

3. **Switching oracle.** Wherever `θ|p′(sz − c)| ≤ ‖∇F(x)‖`, return the base reply padded with a zero `z`-component. Elsewhere, return the true gradient direction plus the base noise.
   - The bias is then `−κθ p′ e_z`, orthogonal to `∇F`.
   - Because `κ² = m/(1−m)`, the condition `‖b‖² ≤ m‖∇f‖² = m(‖∇F‖² + κ²θ²p′²)` is *exactly* `θ|p′| ≤ ‖∇F‖`.
   - The noise is the base noise, whose variance is at most `M‖∇F‖² + σ² ≤ M‖μ‖² + σ²` ([admissibility](../Proofs/BiasedLowerAdmissible.lean)).

4. **Hiding and failure.**
   - On the good event the reply never depends on `(s, z)`, so the composite execution coincides with the projected run of the base chain ([`comp_eq_true`](../Proofs/BiasedLowerBound.lean)). The output's `z` is therefore independent of `s`.
   - Summing over the two signs gives `‖∇f(x̂)‖ ≥ max(3ε_a, 0.99κθ/2)` on average.
   - Averaging over embeddings and coins produces one instance with `E‖∇f(x̂)‖ > ε`. The constant check is `(49/64)·max(6ε_a, 0.99κθ) > 2ε`, [`failure_constant`](../Proofs/BiasedLowerInstance.lean).
   - The base chain at accuracy `ε_a`, with `ε_a² ∈ [r, 25r/9]`, needs `LΔ(1 + M + σ²/ε_a²)/ε_a² ≳ LΔ(1+M+σ²/r)/r` calls ([`budget_le`](../Proofs/BiasedLowerBound.lean)).

The mechanism is a simple but, as far as we can tell, new observation. A relative-bias budget scales with `‖∇f‖` and can hide a slope proportional to the visible gradient floor. That shrinks the effective target accuracy from `ε` to `ε√(1−m)`, in every term of the unbiased complexity.

## Why standard reductions do not give the bound

- **Unbiased lower bounds** (Arjevani et al., Math. Program. 2023; repository ABC pair) contain no `m`.
- **Scaled oracles** `g = (1 ± √m)∇f` are admissible, but they lose nothing: they reveal the gradient direction and can be rescaled.
- **Absolute-bias lower bounds** give only floors. Ajalloeian–Stich's Remark 5 and the recent [arXiv:2606.19553](https://arxiv.org/abs/2606.19553) (lower bounds "matching AS" for absolute bias `B`) both fall in this category; the latter's proof of its Theorem 1 sets `M = m = 0` (App. A.2).
- **Compression lower bounds.** Huang–Chen–Yin–Yuan ([NeurIPS 2022, arXiv:2206.03665](https://arxiv.org/abs/2206.03665)) and the follow-up preprint of He–Huang–Chen–Yin–Yuan ([arXiv:2305.07612](https://arxiv.org/abs/2305.07612), unreviewed; Thm 2) prove `Ω(ΔLσ²/(nε²) + ΔL/(δε))`-type bounds for δ-contractive compressors in a distributed model with `n ≥ 2` workers, counting communication rounds. There the algorithm may compress arbitrary messages and the compressors are random. That model differs in oracle, cost and algorithm class. Mapped into the BND class, their hard compressor has `m = (1−δ)²` and `M = (1−δ)/δ`, so it does not address the `M = 0` factor or the `(1−m)⁻²` noise term.
- **Inexact-gradient method analyses** are upper bounds or method-specific worst-case analyses:
  - the norm condition of Carter 1991;
  - adaptive sampling (Byrd–Chin–Nocedal–Wu 2012);
  - adaptive regularization with inexact evaluations for smooth nonconvex problems (Bellavia–Gurioli–Morini–Toint, [SIAM J. Optim. 2019, arXiv:1811.03831](https://arxiv.org/abs/1811.03831)), and its nonsmooth counterpart (Gratton–Simon–Toint, [Math. Program. 2021](https://link.springer.com/article/10.1007/s10107-020-01466-5));
  - performance-estimation analyses of inexact GD (de Klerk–Glineur–Taylor 2020; Vernimmen–Glineur);
  - convex relative-noise lower bounds (Vasin et al., arXiv:2603.12376, convex and strongly convex only).

## Instances and motivation

The class is the standard umbrella for biased gradient estimators. Demidovich et al. tabulate many of them (Tables 2–3). Ajalloeian–Stich's zeroth-order Gaussian-smoothing example (§5) lies in the class with `m = 0` only, so it does not motivate the `m`-factor. What does is the relative-bias parameter `m`, which is the classical relative-accuracy model of inexact first-order methods: Polyak 1987, the norm condition of Carter 1991, and the norm test of adaptive-sampling methods.

A concrete nonlinear instance with `m > 0` arises when gradients come from an inner iterative solver stopped at relative tolerance `√m`. For example, take a smooth value function `f(x) = min_y φ(x, y)` (strongly convex in `y`) with `∇f(x) = ∇_xφ(x, y⋆(x))`. If the inner solver is stopped once `‖∇_xφ(x, ŷ) − ∇f(x)‖ ≤ √m‖∇f(x)‖` (certified, e.g., by an a-posteriori error bound), the returned vector is an `(m, 0)`-biased gradient, and adding minibatch noise in `φ` gives the stochastic version.

The hard bias used here is a deterministic, instance-dependent relative error applied to the exact gradient. Equivalently, it is a deterministic `(1−m)`-contractive compression of the exact gradient chosen by the adversary.

## Limitations

- **Oracle.** The theorem concerns gradient-only oracles, which is the AS/BND model. With exact function values the decoy direction could be detected, since `p(sz − c)` changes the value. Whether value access can beat `1/(1−m)` (for instance at a `min{1/(1−m), d}`-type cost) is open.
- **Constants and dimension.** Constants are loose (`2^60`) and the dimension requirement `d ≳ (LΔ(1+M+σ²/r)/r)^4` is sufficient, not shown necessary. Both are inherited from the base chain.
- **Floor.** The theorem is stated in the regime `16ζ² ≤ (1−m)ε²` where the upper bound is meaningful. It does not use `ζ` at all.
- **Weaker assumptions.** The weaker Biased-ABC assumption of Demidovich et al. (alignment `⟨∇f, Eg⟩ ≥ b‖∇f‖²` plus a second-moment bound) has the upper bound `LΔ B/(b²ε²) + …`. The decoy argument gives only `LΔ(1+B)/(bε²)` there. The exact `b`-dependence under that assumption remains open.
- **Literature access.** OpenReview pages for ICLR 2027 submissions could not be checked systematically.

## How the requirements are met

- **Almost tight upper and lower bounds in `Template`/`TemplateLowerBound`.** Both theorems use the same objective class, oracle, cost (one call = one stochastic gradient) and criterion. Every term of the rate appears in both budgets. The bounds match up to universal constants with no logarithms.
- **Practical setup.** Biased gradient oracles arise from compression, approximate inner solves stopped at a relative tolerance, and inexact derivatives (zeroth-order smoothing contributes only absolute bias, `m = 0`). The (m, ζ², M, σ²) class is the standard model for them. It is new to this repository, and its `m`-dependence was not settled in the literature.
- **Reuse of techniques.** The randomized chain, coin masking and counting argument are the repository's ABC lower-bound machinery, used white-box. The decoy and switching oracle are new.
- **Overlap check.** The repository already has relative-error gradient results, but only upper bounds for convex, strongly convex, quasar-convex or PŁ objectives:
  - [AcceleratedRelativeErrorConvex](AcceleratedRelativeErrorConvex.md) and its relatives on [`RelativeErrorSmoothConvex`](../Setups/RelativeErrorSmoothConvex.lean);
  - [AcceleratedInexactStronglyConvex](AcceleratedInexactStronglyConvex.md);
  - [AcceleratedRelativeQuasar](AcceleratedRelativeQuasar.md);
  - the PŁ discrepancy setup [`RelativeDiscrepancyPL`](../Setups/RelativeDiscrepancyPL.lean).

  In the convex class, the note of [AcceleratedRelativeErrorConvex](AcceleratedRelativeErrorConvex.md) and open PR #266 show that nesting reduces the small-`α` penalty, and the convex class complexity is left open there. Our hard instance is a nonconvex chain, so it says nothing about the convex class. Conversely, those results do not bound nonconvex stationarity.

  The repository's unbiased relative-variance results ([MixedRelativeSmoothNonconvex](MixedRelativeSmoothNonconvex.md), [FairRelativeEnergyNonconvex](FairRelativeEnergyNonconvex.md)) concern the `M`-type noise term, not bias.

  We found no repository theorem or open pull request with a nonconvex biased-gradient lower bound. We checked main at the base and the open PRs (#257–#271, #215, #4) on 2026-11-26.
