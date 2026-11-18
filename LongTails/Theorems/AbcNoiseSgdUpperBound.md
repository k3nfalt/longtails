# Tight complexity of nonconvex stochastic optimization under expected-smoothness (ABC) noise — SGD upper bound

Lean theorem: [`AbcNoiseSgdUpperBound.lean`](AbcNoiseSgdUpperBound.lean) (`result : Convergence spec budget`).
Setup: [`../Setups/AbcNoiseNonconvex.lean`](../Setups/AbcNoiseNonconvex.lean).
Algorithm: [`../Algorithms/AbcSgd.lean`](../Algorithms/AbcSgd.lean) (`sampledSgd`).
Proofs: [`../Proofs/AbcSgdRate.lean`](../Proofs/AbcSgdRate.lean), [`../Proofs/AbcSgdUpper.lean`](../Proofs/AbcSgdUpper.lean), [`../Proofs/AbcSgdConvergence.lean`](../Proofs/AbcSgdConvergence.lean).
Matching lower bound: [`AbcNoiseLowerBound.lean`](AbcNoiseLowerBound.lean) and its note.

## Setting

`E` is any real Hilbert space (complete, second countable, Borel). The objective `f` is differentiable with an `L`-Lipschitz gradient. It has infimum `f⋆ = inf f`, and `f(x₀) − f⋆ ≤ Δ`. The oracle is IID: one call at `x` returns `g(x, ω)` for a fresh sample `ω`, and `g` is jointly measurable, integrable, unbiased, with

```
E_ω ‖g(x,ω) − ∇f(x)‖² ≤ 2A (f(x) − f⋆) + B ‖∇f(x)‖² + C   for every x.
```

This is Khaled–Richtárik's ABC / expected smoothness condition (TMLR 2023, [arXiv 2002.03329v3](https://arxiv.org/abs/2002.03329), Assumption 2; expected smoothness originates with Gower et al., ICML 2019, [arXiv 1901.09401](https://arxiv.org/abs/1901.09401)) in variance form: their second-moment constant `B_KR` corresponds to `B = max(B_KR − 1, 0)`. The algorithm knows `L, A, B, C, Δ, ε, x₀`. Accuracy is measured as `E‖∇f(x̂)‖ ≤ ε`.

## Algorithm and guarantee

`sampledSgd` draws `τ` uniformly from `{0, …, K}` with its own seed, runs `x_{t+1} = x_t − η g(x_t, ω_t)` for `K+1` oracle calls, and outputs `x_τ`. The tuning is

```
K = ⌈144 L Δ (1 + B + A Δ/ε² + C/ε²)/ε²⌉,    η = 1 / max{ L(1+B), √(L A (K+1)), 6 L C/ε² }.
```

`result` proves `E‖∇f(x_τ)‖ ≤ ε` within

```
budget = ⌈144 L Δ (1 + B + A Δ/ε² + C/ε²)/ε²⌉ + 1
```

oracle calls (every call of the execution is counted). The proof shows, by induction over the product of the first `K+1` samples, that `E Σ_{t≤K} ‖∇f(x_t)‖² ≤ (2/η) ρ^{K+1} (f(x₀) − f⋆) + LηC(K+1) ρ^{K+1}`, with `ρ = 1 + LAη²`. The one-step bound is `E f(x − ηg) − f⋆ ≤ ρ(f(x) − f⋆) − (η/2)‖∇f(x)‖² + Lη²C/2` (`AbcSgdRate.one_step`). The step-size choice gives `ρ^{K+1} ≤ e ≤ 3`, `6Δ/(η(K+1)) ≤ ε²/2` and `3LηC ≤ ε²/2`. Jensen then turns the second-moment bound `E‖∇f(x_τ)‖² ≤ ε²` into the stated first-moment bound. The IID stream is abstract: its product representation on the first `K+1` coordinates is derived from independence and the marginals (`AbcSgdRate.iid_prefix_law`).

## Contribution of this file

The rate is Khaled–Richtárik's Theorem 2 / Corollary 1, `O((LΔ/ε²)·max{1+B, AΔ/ε², C/ε²})`; see also Kawamoto–Iiduka ([arXiv 2510.20608](https://arxiv.org/abs/2510.20608)) for further SGD upper bounds under expected smoothness. Its only difference is the output rule: a uniformly sampled iterate instead of their weighted sampling. **The upper bound is not claimed as new.** It is formalized here so that the repository contains both halves of the tight characterization:

```
Θ( (L Δ/ε²) · (1 + B + A Δ/ε² + C/ε²) )   oracle calls,
```

for all randomized algorithms (up to universal constants and with no logarithms), in the regime of the lower-bound setup (`2^26 ε² ≤ LΔ`, polynomially large dimension). The new mathematical content is the lower bound's `A`-term; see [`AbcNoiseLowerBound.md`](AbcNoiseLowerBound.md). The lower-bound setup is a parameter restriction of this one (`AbcNoiseInclusion.highDimensionalInclusion`), so this upper bound applies verbatim to every hard instance.

## How the pair meets the strict research direction

The pair proves almost tight upper and lower bounds, both in the repository, for a popular setup: SGD's standard general noise model. The upper bound is the known rate, formalized here. The lower bound is new; it closes the problem up to a universal constant factor `144·2^53`, with no logarithms, in the lower-bound regime. Details are in [`AbcNoiseLowerBound.md`](AbcNoiseLowerBound.md).

## Limitations

* Expected first-moment accuracy only; no high-probability version.
* Step size and horizon use `L, A, B, C, Δ, ε`; no adaptivity is claimed.
* Constants are not optimized.
