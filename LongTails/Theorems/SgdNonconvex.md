# Tutorial SGD pipeline smoke test

This result installs the prepared solution from `tutorial/ToBeDiscovered` to test
research PR verification and automatic novelty reviews. It is a classical SGD
bound, not a claim of a new mathematical contribution. A low novelty rating is
expected and should not prevent the review workflow from completing.

For an L-smooth objective with initial gap at most Δ above a global lower bound,
IID unbiased stochastic gradients with variance at most σ², and ε > 0, the
algorithm uses step size η = 1 / (L + 2Lσ²/ε²). It makes exactly
K = 1 + ⌈4LΔ/ε² + 8LΔσ²/ε⁴⌉ stochastic-gradient calls and returns a uniformly
random pre-update iterate. The theorem proves E[‖∇f(output)‖²] ≤ ε².

The setup reuses the library's IID and stochastic-gradient assumptions.
The supporting proofs connect the selected iterate to actual oracle execution
and derive the expected descent, output guarantee, and explicit budget.
