# High-probability stationarity under bounded variance: lower bound

Lean: [`HighProbabilityStationarityLowerBound.lean`](HighProbabilityStationarityLowerBound.lean)
(theorem `result : NonConvergence spec budget`). Setup:
[`Setups/HighDimensionalHighProbabilityStationarity.lean`](../Setups/HighDimensionalHighProbabilityStationarity.lean).
Proofs:

- [`Proofs/HighProbabilityChainFailure.lean`](../Proofs/HighProbabilityChainFailure.lean)
- [`Proofs/HighProbabilityTwoPointFailure.lean`](../Proofs/HighProbabilityTwoPointFailure.lean)
- [`Proofs/HighProbabilityLowerAssembly.lean`](../Proofs/HighProbabilityLowerAssembly.lean)

It is paired with the upper bound
[`HighProbabilityStationarityUpperBound`](HighProbabilityStationarityUpperBound.md).

## Setup

The class is the instance class of the upper-bound setup restricted to
`E = EuclideanSpace ℝ (Fin d)`, through `toGeneral`. It consists of:

- `f` with an `L`-Lipschitz gradient and `f(x0) − inf f ≤ Δ`;
- an IID unbiased oracle with variance `≤ σ²`;
- the success criterion `P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ`, with a measurable output.

`valid` requires all of the following:

- `L > 0`, `σ ≥ 0`, `ε > 0` and `0 < δ ≤ 1/4`;
- `2^54 ε² ≤ LΔ`, a nontrivial-accuracy condition;
- `d ≥ 2^40 (1 + LΔ(1+σ²/ε²)/ε²)^4`, which gives the chain room in high dimension.

This regime is nonempty: take `L = Δ = 1` and `ε` small, with `d` large.

## Result

For every valid parameter, every randomized algorithm, and every budget `b`
up to the stated budget, there is an admissible instance on which the algorithm fails. Here
failure means that it does not output a measurable ε-stationary point with probability
`≥ 1 − δ`. The budget is

```
⌊(LΔ(1 + σ²/ε²) + σ² log(1/(4δ))) / (2^54 ε²)⌋
```

The hard instance depends on the algorithm and the budget, but not on its realized seed.

## Hard instances

1. **High-probability masked chain** (`HighProbabilityChainFailure`). This term is
   `LΔ(1+σ²/ε²)/ε²`. It reuses the repository's ABC-noise masked-chain construction
   (Arjevani et al. type) with `A = B = 0` and `C = σ²`.
   - The existing argument shows that below the chain budget the probability of
     `‖∇f(x̂)‖ ≤ ε` is below `3/4`.
   - Since `δ ≤ 1/4`, this already violates `1 − δ`.
2. **Rare-reveal two-point instance** (`HighProbabilityTwoPointFailure`). This term is
   `σ² log(1/δ)/ε²`.
   - *The pair.* The two functions are
     `f_s(x) = (L/2)⟨e, x−x0⟩² + 2sε⟨e, x−x0⟩`, for `s = ±1`.
   - *Why they are distinguishable only at the output.* No point is `ε`-stationary for both
     signs.
   - *The oracle.* It returns the exact quadratic part plus `2sε·R(ω)`, where `R(ω) = 1/p` with
     probability `p = 4ε²/(σ² + 4ε²)` and `0` otherwise. This oracle is unbiased and has
     variance exactly `σ²`.
   - *Why the algorithm fails.* With `N ≤ σ² log(1/(4δ))/(8ε²)` calls, no sample reveals
     the sign with probability `(1−p)^N > 2δ`.
   - *The sign choice.* On that event the run is identical under both signs. One sign
     therefore fails with probability `> δ`.
3. **Assembly** (`HighProbabilityLowerAssembly`). For a budget below the stated formula,
   two cases arise:
   - the budget is below the chain budget, so the chain instance fails;
   - otherwise the budget is below the two-point budget (`budget_split`), so the
     two-point instance fails.

## Contribution and comparison

**What is known.**

- `Ω(LΔ/ε² + LΔσ²/ε⁴)` is the lower bound of Arjevani et al. (Math. Program. 2023), stated
  for expected accuracy or constant success probability.
- The two-point `σ² log(1/δ)/ε²` term is folklore in the mean-estimation sense.

**What is new here.**

- Extending the chain bound to every success level `1 − δ ≤ 3/4` is routine, since
  failure probability `≥ 1/4 > δ` already rules out success.
- What is new is the formalization against the exact high-probability, single-output
  criterion, combined with the two-point `σ² log(1/δ)/ε²` term into one budget that pairs
  with the upper bound.

**How it pairs with the upper bound.**

- The upper bound is
  `O((1+σ²/ε²)(LΔ/ε² + ℓ log³(2+ℓ)) + √(LΔ)ℓ/ε)`, with `ℓ = log(16/δ)`.
- The pair determines the high-probability complexity `Θ((LΔ/ε²)(1+σ²/ε²))` of the
  class when `ℓ log³(2+ℓ) ≲ LΔ/ε²` and `ℓ ≲ (√(LΔ)/ε)(1+σ²/ε²)`. In that regime the
  complexity is δ-free.
- When `σ ≳ ε`, the pair agrees up to a `log³(2+log(1/δ))` factor on the confidence term
  and the corner term `√(LΔ)ℓ/ε`.
- When `σ ≲ ε`, the gap on the confidence term is unbounded. At `σ = 0` the upper bound
  keeps `ℓ log³(2+ℓ) + √(LΔ)ℓ/ε`, while this lower bound has no `δ`-dependent term.

**Differences between the two theorems.**

- The lower bound uses a high-dimensional Euclidean subclass and the extra `valid`
  conditions above.
- The upper bound holds on the full general-space class.
- The oracle model and accuracy criterion are the same.

## Limitations

- The lower bound has no `ℓ·log³` and no `√(LΔ)ℓ/ε` terms. When `σ = 0` the confidence
  term vanishes, which is consistent with deterministic first-order methods.
- The constant `2^54` is loose.
- The dimension requirement is polynomial, and comes from the chain construction.
