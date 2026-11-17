This theorem restates a known upper bound in the setup of the new lower bound, so that the pair is stated for one model. It is not a new upper-complexity claim.

The [theorem](HighDimensionalStrongQuasarUpperBound.lean) uses [HighDimensionalStrongQuasar](../Setups/HighDimensionalStrongQuasar.lean). That setup has the admissible instances and expected-gap criterion of [RelativeGradientStrongQuasar](../Setups/RelativeGradientStrongQuasar.lean) at relative error δ = 0, in ℝᵈ:

- L-smooth f;
- exact gradient oracle;
- initial gap at most Δ;
- (γ, μ)-strong quasar-convexity with respect to a global minimizer x⋆.

The algorithm is the repository's randomized continuized accelerated method [`RelativeQuasar.accelerated`](../Algorithms/RelativeQuasar.lean), run on the public parameters with δ = 0. It returns its primal state after

**⌈32√(L/μ)/γ⌉ · ⌈log₂(1 + 2Δ/(γε))⌉ gradient calls,**

with integrable gap and expected gap at most ε. [StrongQuasarChainUpper](../Proofs/StrongQuasarChainUpper.lean) proves that the setup's parameter conditions imply the conditions of the original guarantee. It also proves that this one-line budget equals the original call count at δ = 0: the error terms vanish, and both factors are at least one because Δ > 0. The theorem body repeats the execution argument of [AcceleratedRelativeQuasar](AcceleratedRelativeQuasar.lean) with these parameters.

The order γ⁻¹√κ log(1/ε) is due to earlier work:

- [Hinder, Sidford and Sohoni, COLT 2020](https://proceedings.mlr.press/v125/hinder20a.html), Theorem 1, up to a log(γ⁻¹κ) binary-search factor and using function values;
- [Wang and Wibisono, ICLR 2023](https://openreview.net/pdf?id=yYbhKqdi7Hz), Theorem 2 and Corollary 2, by continuized acceleration. Their bounds are a continuized-time expectation and a high-probability bound.

The fixed-budget expected-gap form above is the repository's own theorem.

The upper guarantee holds without the dimension or regime conditions of the setup; those conditions are needed only by the lower bound.

The companion [lower bound](HighDimensionalStrongQuasarLowerBound.lean) has the same setup, oracle and criterion. Every randomized gradient method needs Ω(γ⁻¹√κ log(Δ/(γ√κε))) calls in the stated high-dimensional regime. The two bounds therefore agree up to a universal constant when ε ≤ Δ/(10⁶γκ), and up to a factor O(log κ) otherwise. See the [lower-bound note](HighDimensionalStrongQuasarLowerBound.md) for the comparison with prior lower bounds and the construction.
