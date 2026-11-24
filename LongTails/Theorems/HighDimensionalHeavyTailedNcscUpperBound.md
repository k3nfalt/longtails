# Upper bound for heavy-tailed NC–SC minimax on the high-dimensional lower-bound specification

The [theorem](HighDimensionalHeavyTailedNcscUpperBound.lean) proves `Convergence spec budget` for the
[high-dimensional heavy-tailed NC–SC setup](../Setups/HighDimensionalHeavyTailedNcsc.lean). This is the setup on which
the matching [lower bound](HeavyTailedNcscLowerBound.lean) is proved.

This is not a new optimization result. It specializes the repository's accelerated upper bound
[HeavyTailedNcscAccelerated](HeavyTailedNcscAccelerated.lean) (PR #143), which is not modified, to the restricted
public data:
- E = F = ℝ^d, Ω = ℝ, x0 = y0 = 0;
- the extra lower-bound regime conditions in `valid`.

The restricted `admissible` and `successful` predicates are definitionally those of the general setup at
`toGeneral q`. The theorem runs the same algorithm, `saddleAlgorithm`, and its public budget is the PR #143 formula
written with local names. With κ = L/μ, r = p/(p−1), A = LΔ/ε², u = σ/ε, Q = log(2 + κ³L(Δ + G²/μ)/ε²) and
Λ = 1 + log(2 + κ + 1/δ + A + (κu)^r + Q), the budget is

  ⌈(2^80 r)^{r+2} Λ^{2r+3} [ √κ(1 + A + Q) + (A κ^{r/2} + κ^r) u^r ]⌉

joint stochastic-gradient calls. This is enough to make P(‖∇Φ(X)‖ > ε) ≤ δ for the returned point X.

The purpose of the file is to state both halves of the characterization on one specification, so that the
parameter ranges, oracle model, and accuracy criterion of the upper and lower bounds coincide. On the regime σ ≥ ε,
the two budgets agree up to p-dependent constants and the polylogarithmic factors Λ^{2r+3} and Q. The
[lower-bound note](HeavyTailedNcscLowerBound.md) gives the comparison and the literature context.
