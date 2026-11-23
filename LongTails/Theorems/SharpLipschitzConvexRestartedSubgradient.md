This is the upper-bound half of a tight pair for **weakly sharp Lipschitz convex minimization**. The matching lower bound is [SharpLipschitzConvexLowerBound](SharpLipschitzConvexLowerBound.lean), and its note explains the new contribution. The upper bound here is the classical restarted subgradient guarantee. It is **not** a new rate. The restarted subgradient argument is textbook; it is formalized here only so that both directions use the same oracle model, the same accuracy criterion and the same constants.

## Setup

The [main theorem](SharpLipschitzConvexRestartedSubgradient.lean) uses [SharpLipschitzConvex](../Setups/SharpLipschitzConvex.lean). Its public parameters are d, L, μ, D, ε and x₀ ∈ ℝᵈ; `valid` requires 0 < μ ≤ L, D > 0 and ε > 0. An instance is a function f : ℝᵈ → ℝ with:

- **Convexity:** f is convex on ℝᵈ.
- **Lipschitz continuity:** |f(x) − f(y)| ≤ L‖x − y‖.
- **Initial distance:** some minimizer x⋆ of f satisfies ‖x₀ − x⋆‖ ≤ D.
- **Global weak sharpness:** for every x there is a minimizer z with μ‖x − z‖ ≤ f(x) − f(z). Equivalently, f(x) − f⋆ ≥ μ·dist(x, argmin f), because every minimizer has value f⋆ and the infimum over minimizers is attained for a closed convex argmin.
- **Oracle:** a query at x returns (f(x), g(x)), where g is *any* subgradient selection, that is, f(y) ≥ f(x) + ⟨g(x), y − x⟩ for all y. The selection is fixed by the instance; it may not depend on the history or a seed.

Success means that the output's objective gap f(x̂) − f(x⋆) is integrable and has expectation at most ε, for some minimizer x⋆.

Weak sharpness is the standard error bound for nonsmooth convex problems. It is Polyak's "sharp minimum" condition (Polyak, *Introduction to Optimization*, 1987, Ch. 5). It is the θ = 1 case of the Hölderian error bound, and it is used, for example, in [Davis, Drusvyatskiy, MacPhee and Paquette, JOTA 2018](https://arxiv.org/abs/1803.02461), [Yang and Lin, JMLR 2018](https://arxiv.org/abs/1512.03107) and [Wang, arXiv 2512.13863 v1](https://arxiv.org/abs/2512.13863). Typical examples are ‖Ax − b‖₁ and ‖Ax − b‖_∞ regression with a consistent system, polyhedral (piecewise-linear) convex functions, hinge-loss feasibility problems, and the distance to a closed convex set. Wang's class F_{h,L,D} requires the error bound only within distance D of argmin f. The present setup requires it globally, which is a smaller class. A lower bound for the smaller class is therefore the stronger statement, and that is what the companion theorem proves.

## Algorithm and theorem

[restartedSubgradient](../Algorithms/RestartedSubgradient.lean) runs the subgradient method in phases of length T = ⌈4L²/μ²⌉.

- Phase k starts from the previous phase's average y_k and uses the constant step γ_k = (D/2^k)/(L√T).
- The phase output y_{k+1} is the average of its T iterates.
- The algorithm returns y_K after K = ⌈log₂⌈μD/ε⌉⌉ + 1 phases. It uses L, D and T, which depends on L and μ. It does not use f⋆ or function values.

The theorem proves that, for every admissible instance and every subgradient selection, the output satisfies f(x̂) − f⋆ ≤ ε deterministically within

**budget = ⌈4L²/μ²⌉ · (Nat.clog 2 ⌈μD/ε⌉₊ + 1) = O((L/μ)² · (1 + log(μD/ε))) subgradient calls,**

where Nat.clog 2 n = ⌈log₂ n⌉.

The induction in [RestartedSubgradient](../Proofs/RestartedSubgradient.lean) is the standard one:

1. If dist(y_k, argmin f) ≤ D/2^k, then the averaged subgradient bound gives f(y_{k+1}) − f⋆ ≤ L(D/2^k)/√T ≤ μD/2^{k+1}.
2. Sharpness converts this to dist(y_{k+1}, argmin f) ≤ D/2^{k+1}.
3. After K phases the gap is at most μD/2^K ≤ ε.

The output is deterministic, so integrability and the expectation are immediate.

## What was known

This rate is classical, and no novelty is claimed for it.

- Restart schemes exploiting growth conditions go back to Nemirovski and Nesterov (1985), in the smooth setting. For sharp nonsmooth problems, restarted and step-decay subgradient methods are analysed by Yang–Lin and Davis et al. below.
- Polyak's step-size subgradient method attains the same linear rate (1 − μ²/L²)^{n/2} in distance (Polyak 1969; restated as Wang's Theorem 1).
- [Davis et al., JOTA 2018](https://arxiv.org/abs/1803.02461) analyse the geometrically decaying step-size variant (their results for sharp, possibly weakly convex functions specialize to the convex case).
- [Yang and Lin, JMLR 2018](https://arxiv.org/abs/1512.03107) prove restarted subgradient (RSG) bounds under local error bounds.

The repository version uses a convenient but non-optimized constant (4 in T and base-2 halving). The upper bound does not use the dimension condition or the other restrictions of the lower-bound setup. Those restrictions only determine where the pair is stated.

## Relation to the lower bound

The lower bound uses the setup [HighDimensionalSharpLipschitzConvex](../Setups/HighDimensionalSharpLipschitzConvex.lean). It has the same Params, admissible instances, oracle and success criterion as this setup, by definition. Its `valid` adds 96μ ≤ L, ε ≤ μD and a dimension condition. Every lower-bound parameter point is therefore a valid point here, and the two budgets can be compared directly.

On that regime, with κ = L/μ ≥ 96 and y = μD/ε ≥ 1:

- When the lower budget ⌊κ²(1 + log y)/4608⌋ is at least 1, the floor loses at most a factor 2, so the lower budget is at least κ²(1 + log y)/9216.
- The upper budget is at most 5κ²(log₂ y + 3) ≤ 15κ²(1 + log y). This uses ⌈4κ²⌉ ≤ 5κ² and Nat.clog 2 ⌈y⌉ ≤ log₂ y + 2.
- So the ratio of upper to lower budget is at most 15 · 9216 ≈ 1.4·10⁵, uniformly over the regime, including μD/ε close to 1.
- The constants were not optimized.
