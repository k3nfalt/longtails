# Biased SGD under (m, ζ²)-bias and (M, σ²)-noise: upper bound

Lean files:
- [theorem](BiasedNoiseSgdUpperBound.lean)
- [setup](../Setups/BiasedNoiseNonconvex.lean)
- algorithm: the repository's [uniform-output SGD](../Algorithms/AbcSgd.lean)
- proofs: [one step and accumulated gradient loss](../Proofs/BiasedSgdRate.lean), [tuning and assembly](../Proofs/BiasedSgdConvergence.lean)
- companion lower bound: [BiasedNoiseLowerBound](BiasedNoiseLowerBound.md)

## Setup

`E` is any real complete inner-product space (Borel, second countable), so every `ℝ^d` and every separable Hilbert space is covered. The objective `f : E → ℝ` is differentiable with an `L`-Lipschitz gradient. It is bounded below, with `f⋆ = inf f`, and `f(x₀) − f⋆ ≤ Δ`.

Each call at `x` returns `g(x, ω)` for a fresh IID sample. The map `g` is jointly measurable and integrable, with mean `μ(x)`. The two conditions on it are, verbatim, Assumptions 4 and 3 of [Ajalloeian–Stich, arXiv:2008.00051](https://arxiv.org/abs/2008.00051), i.e. the BND class of [Demidovich et al., NeurIPS 2023](https://arxiv.org/abs/2305.16296):

```
‖μ(x) − ∇f(x)‖² ≤ m‖∇f(x)‖² + ζ²   (0 ≤ m < 1),
E‖g(x,ω) − μ(x)‖² ≤ M‖μ(x)‖² + σ².
```

`valid` also requires `16ζ² ≤ (1 − m)ε²`. Ajalloeian and Stich (Remark 5) show that gradient norms below the error floor `ζ²/(1 − m)` are unreachable in general. Success means `E‖∇f(x̂)‖ ≤ ε` for a measurable output.

## Algorithm and guarantee

Put `r = (1 − m)ε²`. The method runs `K = ⌈16LΔ(1 + M + σ²/r)/r⌉` steps of SGD

```
x_{t+1} = x_t − γ g(x_t, ω_t),        γ = 1 / max{ L(1 + M), 4Lσ²/r }.
```

It returns `x_τ` for an independent uniform index `τ ∈ {0, …, K}`. Every one of the `K + 1` calls is counted, so the budget is

```
budget = ⌈ 16 L Δ (1 + M + σ²/r) / r ⌉ + 1.
```

`result : Convergence spec budget` holds on the general setup.

## Proof

1. **One step** ([`one_step_biased`](../Proofs/BiasedSgdRate.lean)). This is the AS modified descent lemma. Write `g = μ + n`, use `Lγ(1 + M) ≤ 1`, and use the identity `−⟨∇f, μ⟩ + ‖μ‖²/2 = (‖μ − ∇f‖² − ‖∇f‖²)/2`. Together they give

   ```
   E f(x − γg) − f⋆ ≤ f(x) − f⋆ − (γ/2)(1 − m)‖∇f(x)‖² + (γ/2)ζ² + Lγ²σ²/2.
   ```

2. **Accumulated loss** ([`gradLoss_bound_biased`](../Proofs/BiasedSgdRate.lean)). By induction over the product law of the samples,

   ```
   E Σ_{t ≤ K} ‖∇f(x_t)‖² ≤ 2Δ/(γ(1 − m)) + (K + 1)(ζ² + Lγσ²)/(1 − m).
   ```

   The induction reuses the repository's gradient-loss recursion and IID prefix law.

3. **Tuning** ([`BiasedSgdConvergence`](../Proofs/BiasedSgdConvergence.lean)). The uniform output has `E‖∇f(x̂)‖² ≤ ε²/2 + ε²/16 + ε²/4 < ε²`: the first term comes from the initial gap, the second from the ζ-floor and the third from the noise. Jensen's inequality then gives `E‖∇f(x̂)‖ ≤ ε`.

## Contribution and comparison

The rate is Ajalloeian–Stich's Theorem 4: `O((M + 1)LΔ/((1 − m)ε²) + LΔσ²/((1 − m)²ε⁴))` iterations in our normalisation, in the floor regime. It is formalised here with an explicit, log-free budget. No algorithmic novelty is claimed.

The contribution of the pair is the matching lower bound in [BiasedNoiseLowerBound](BiasedNoiseLowerBound.md). It shows that every term of this budget, including the `1/(1 − m)` and `1/(1 − m)²` factors, is necessary for every randomized gradient-only algorithm. Plain SGD is therefore minimax optimal on the class up to universal constants. The two budgets satisfy `upper ≤ 2^64 · (lower + 1) + 2` on the lower-bound regime.

## Limitations

- The upper bound is a known guarantee for a standard algorithm.
- Constants are not optimised.
- The step size and horizon use `L, m, M, σ, Δ, ε`. No adaptivity is claimed.
- The guarantee is for a uniformly random iterate. Last-iterate and high-probability versions are not treated.
