# Smoothed-AGDA reaches Moreau stationarity of nonconvex–PŁ minimax problems in κℓΔ/ε² + κ²ℓΔσ²/ε⁴ gradient calls

The [main theorem](StochasticNonconvexPLUpperBound.lean) shows that single-loop stochastic Smoothed-AGDA, run for

    2⌈ 2⁴⁴ · ℓ²Δ/(με²) · (1 + ℓσ²/(με²)) ⌉   oracle calls,

returns a point x̂ with E‖∇Φ_{1/(2ℓ)}(x̂)‖ ≤ ε on every smooth minimax problem that is nonconvex in x and μ-PŁ in y, with an unbiased stochastic gradient oracle of variance at most σ². Here Φ(x) = max_y f(x, y) and κ = ℓ/μ.

The companion [lower theorem](StochasticNonconvexPLLowerBound.lean) ([note](StochasticNonconvexPLLowerBound.md)) proves that every randomized algorithm needs ⌊ℓ²Δ/(2⁹⁴με²)·(1 + ℓσ²/(2⁵⁹με²))⌋ calls on a restriction of the same setup. The rate Θ(κℓΔ/ε² + κ²ℓΔσ²/ε⁴) is therefore optimal for this criterion, without logarithmic factors.

## How this meets the task requirement

The task asked for an almost tight upper and lower bound pair for an important, popular setup, stated with `Template` and `TemplateLowerBound`. This theorem is the upper half. The rate is the one of Yang, Orvieto, Lucchi and He, AISTATS 2022 ([arXiv:2112.05604](https://arxiv.org/abs/2112.05604), Theorem 4.1); the new mathematical content of the pair is in the lower bound. What this half adds is a self-contained proof for the Moreau criterion with explicit constants, a returned iterate that needs no post-processing, and the formal `Convergence` statement that the lower bound is matched against.

## Setup

[StochasticNonconvexPL](../Setups/StochasticNonconvexPL.lean). E is a finite-dimensional real inner product space, F a separable real Hilbert space, and an instance is f : E × F → ℝ such that

- f is differentiable in each block and both partial gradients are jointly ℓ-Lipschitz, ‖g(z) − g(z′)‖ ≤ ℓ(‖x − x′‖ + ‖y − y′‖);
- 2μ(f(x, y′) − f(x, y)) ≤ ‖∇_y f(x, y)‖² for all x, y, y′ (PŁ in y);
- the maximum over y is attained for every x and Φ = max_y f is bounded below;
- one oracle call at (x, y) returns (G_x, G_y), jointly measurable, unbiased, with E(‖G_x − ∇_x f‖² + ‖G_y − ∇_y f‖²) ≤ σ²; samples are IID across calls;
- 2Φ(x₀) − inf Φ − f(x₀, y₀) + ‖∇_x f(x₀, y₀)‖²/ℓ ≤ Δ.

Validity is μ > 0, μ ≤ ℓ, σ ≥ 0, Δ ≥ 0, ε > 0. The algorithm may use ℓ, μ, σ, Δ, ε, x₀, y₀. There is no `allowedAlgorithm` restriction.

**Accuracy.** Integrability of 2ℓ·dist(x̂, prox(x̂)) and E[2ℓ·dist(x̂, prox(x̂))] ≤ ε, where prox(x̂) is the set of minimizers of Φ(x) + ℓ‖x − x̂‖². Under the assumptions the minimizer is unique and this is E‖∇Φ_{1/(2ℓ)}(x̂)‖ ≤ ε.

## Algorithm

[nonconvexPLSmoothedAgda](../Algorithms/NonconvexPLSmoothedAgda.lean). With τ = 1/(ℓ(3 + 2²³ℓσ²/(με²))) and n = ⌈2⁴⁴(ℓ²Δ/(με²))(1 + ℓσ²/(με²))⌉, starting from (x₀, y₀, z₀ = x₀), each iteration does

    x⁺ = x − τ(G_x(x, y; ξ) + 2ℓ(x − z)),
    y⁺ = y + (τ/32)·G_y(x⁺, y; ξ′),
    z⁺ = z + (τμ/6144)(x⁺ − z),

with two fresh oracle calls. The output is z_J for an index J drawn uniformly from {0, …, n} by the algorithm's own seed. The total is 2n calls, which is the public budget.

## Proof

Let f̂(x, y; z) = f(x, y) + ℓ‖x − z‖², x̂(y, z) its minimizer in x, and x̄(z) the proximal point of Φ at z.

1. **Potential** ([NonconvexPLStep](../Proofs/NonconvexPLStep.lean), [NonconvexPLPath](../Proofs/NonconvexPLPath.lean)). The Smoothed-AGDA potential V = f̂ − 2·min_x f̂ + 2·min_x max_y f̂ decreases in expectation by a multiple of τ‖∇_x f̂‖² + τ‖∇_y f(x̂(y, z), y)‖² + τμ‖x − z‖², up to 4ℓτ²σ² per step. This is the analysis already formalized for two-sided PŁ problems, copied without the x-side PŁ assumption, which that step never used.
2. **Moreau residual** ([NonconvexPLMoreau](../Proofs/NonconvexPLMoreau.lean)). The triangle inequality z − x̄ = (z − x⁺) + (x⁺ − x̂) + (x̂ − x̄), strong convexity of f̂ in x, and the PŁ error bound ℓ²‖x̂(y, z) − x̄(z)‖² ≲ κ‖∇_y f(x̂, y)‖² give

       μτ·(2ℓ‖z − x̄(z)‖)² ≤ 2¹⁹ℓ·(decrease of V) + 24ℓ²τ³μ‖noise‖².

3. **Summation** ([NonconvexPLConvergence](../Proofs/NonconvexPLConvergence.lean), [NonconvexPLUpper](../Proofs/NonconvexPLUpper.lean)). Averaging over the n + 1 candidate indices and using Jensen's inequality gives (E‖∇Φ_{1/(2ℓ)}(z_J)‖)² ≤ 2¹⁹ℓΔ/(μτ(n + 1)) + 2²²ℓ²τσ²/μ, which is at most ε² for the stated τ and n.

The proof also shows that the proximal point is unique and depends continuously on z, which gives measurability and integrability of the criterion.

## Relation to prior work

- **Yang, Orvieto, Lucchi and He, [arXiv:2112.05604](https://arxiv.org/abs/2112.05604), Theorem 4.1 and Corollary 4.1.** Smoothed-AGDA with O(κℓΔ/ε² + κ²ℓΔσ²/ε⁴) calls for stationarity of the game gradients, and a conversion to ‖∇Φ‖ with extra cost. The rate here is theirs. The differences are the criterion (Moreau envelope of Φ, evaluated at the auxiliary iterate z, no conversion step) and the explicit constants.
- **Ha, [arXiv:2610.07814](https://arxiv.org/abs/2610.07814), Proposition E.1.** Restates the Smoothed-AGDA bound for E‖∇Φ(x̂)‖² ≤ ε² with an additional (κ + κ⁴σ²/ε²) log κ term from the post-processing stage. Under the Moreau criterion this term does not appear.
- **Zhang et al., [arXiv:2010.15768](https://arxiv.org/abs/2010.15768).** The smoothing idea for nonconvex–concave problems.
- **Lower bounds.** Pan and Li ([arXiv:2608.26799](https://arxiv.org/abs/2608.26799)) for deterministic algorithms and exact oracles; the companion theorem for randomized algorithms and stochastic gradients.

## Limitations

- The guarantee is for the Moreau envelope measure, which is weaker than ‖∇Φ(x̂)‖ ≤ ε: under these assumptions Φ is differentiable (Nouiehed et al. 2019, Lemma A.5) and ‖∇Φ_{1/(2ℓ)}‖ ≤ 2‖∇Φ‖. No bound for ‖∇Φ(x̂)‖ without post-processing is claimed.
- Δ is the potential-type initialization above, not the primal gap alone.
- The step sizes use ℓ, μ, σ and ε. The constant 2⁴⁴ is not optimized.
- The guarantee is in expectation; no high-probability statement is made.
