# Ball-anchored Newton on the high-dimensional Hessian-stable setup (upper bound of the tight pair)

Lean: theorem [`result`](HessianStableExpectedNewton.lean) (`Convergence LongTails.Setups.HighDimensionalHessianStableSkewMonotone.spec budget`).
- Setup: [`HighDimensionalHessianStableSkewMonotone`](../Setups/HighDimensionalHessianStableSkewMonotone.lean).
- Algorithm: [`BallAnchoredNewton`](../Algorithms/BallAnchoredNewton.lean), unchanged.
- Proofs: reused from [`HessianStableSkewNewton`](HessianStableSkewNewton.lean) (`run_finishes`, `execution_output`, `total_le`).
- Matching lower bound: [`HessianStableNewtonLowerBound`](HessianStableNewtonLowerBound.lean).

## Statement

The class is the same as in [`HessianStableSkewMonotone`](../Setups/HessianStableSkewMonotone.lean):

- monotone `F : ℝ^d → ℝ^d` with `DF = S + H`, where `S` is skew and `H` is symmetric, PSD and Hessian-stable with constant `M`;
- a zero `x⋆` with `‖x₀ − x⋆‖ ≤ D`;
- `‖DF‖ ≤ Λ` on `B(x⋆, 3D + 1/(4M))`.

The oracle has two channels, `F(x)` and `DF(x)`. The deterministic ball-anchored Newton method outputs `x̂` with `E‖F(x̂)‖ ≤ ε`, using on each channel at most

`⌈2^17 (1 + (MD)^{2/3}) · log³(3 + MD + MΛ(D + 1/M)²/ε)⌉`

calls (at most twice that in total). Since the method is deterministic, the expectation equals the almost-sure value.

## What is new here

Nothing about the algorithm or its rate. The guarantee is the repository theorem [`HessianStableSkewNewton`](HessianStableSkewNewton.lean) (see its note for the method, the comparison with Carmon et al. 2020 and Doikov 2023, and the proof). This file only transfers it to the lower-bound setup:

- the space is `ℝ^d` with `d` public;
- success is in expectation;
- `valid` adds regime conditions;
- all parameters, including `Λ` and `d`, are public (the algorithm ignores `Λ`).

The transfer is proved by inclusion. Every valid parameter of the new setup is valid for the old one, the admissible class is identical, and a deterministic almost-sure bound gives an integrable, constant loss.

Together with the new lower bound `⌊(MD/(2^18 log(2 + MD)))^{2/3}⌋` per channel, it shows that `(MD)^{2/3}` is the second-order oracle complexity of the class, up to polylogarithmic factors. The remaining gap is `polylog(MD)·log³(MΛD²/ε)`. This is `polylog(MD)` when `log(MΛD²/ε) = O(log MD)`, but can be as large as `(MD)³` for exp-type curvature with `Λ = e^{Θ(MD)}`; see the lower-bound note.
