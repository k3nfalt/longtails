# Sharp upper bound for stochastic gradient methods under third-order smoothness

The [main theorem](ThirdOrderSmoothStochasticUpperBound.lean) is the upper half of a tight pair. For a nonconvex objective whose gradient, Hessian and third derivative are Lipschitz with constants L₁, L₂, L₃, and a single-query unbiased stochastic gradient oracle with variance at most σ², normalized SGD with a two-lookahead extrapolated momentum finds a point with E‖∇f(x̂)‖ ≤ ε using at most

    ⌈ 100000 · (1 + σ²/ε² + L₁Δ/ε² + (Δσ²/ε³) · M) ⌉   oracle calls,   M = min{ L₁/ε, √(L₂/ε), ∛(L₃/ε) }.

The companion [lower theorem](ThirdOrderSmoothStochasticLowerBound.lean) shows that ⌊Δ·M·(1 + σ²/ε²)/(2¹⁷⁴ε)⌋ calls do not suffice for any randomized algorithm in high dimension. In the noise-dominated regime the two bounds agree up to a universal constant, with no logarithmic factor:

    Θ( (Δσ²/ε³) · min{ L₁/ε, √(L₂/ε), ∛(L₃/ε) } ).

For fixed parameters and small ε this is Θ(Δσ²∛L₃ · ε^(−10/3)).

## What is new and what is not

- **Not new: the exponent ε^(−10/3) and the estimator.** Chuan He, [arXiv:2412.14488v4](https://arxiv.org/abs/2412.14488) (Theorem 2 for p = 3, Theorem 4 for general p), introduced the multi-extrapolated momentum and proved Õ(ε^(−(3p+1)/p)) for objectives with Lipschitz p-th derivative under exactly this oracle. For p = 3 his bound is K ≥ ((20M₃/3ε)·ln(20M₃/3ε))^(10/3) with M₃ = 4(Δ + 19σ² + L₁ + 4L₃² + 2), obtained with parameter-free decaying schedules. The two-lookahead rule used here is his rule with q = 2 extrapolations and constant parameters. He–Lu–Sun–Deng, [arXiv:2506.11214v2](https://arxiv.org/abs/2506.11214) (Theorem 3), extend it to heavy-tailed noise, again with a logarithm and a lumped constant.
- **Earlier use of third-order smoothness under a different oracle.** Yu–Xu–Gu ([NeurIPS 2018](https://proceedings.neurips.cc/paper/2018/hash/fea9c11c4ad9a395a636ed944a28b51a-Abstract.html), [arXiv:1712.06585](https://arxiv.org/abs/1712.06585)) reach Õ(ε^(−10/3)) for approximate local minima using third-order smoothness. Their analysis assumes that every component F(·; ξ) is smooth and uses SCSG variance reduction, which queries the same sample at several points; in that model ε⁻³ is the optimal rate. It is not the single-query bounded-variance model of this result.
- **Not new: the cases governed by L₁ and L₂.** SGD gives O(L₁Δσ²/ε⁴) (Ghadimi–Lan 2013). Normalized SGD with implicit gradient transport gives the sharp O(Δσ²√L₂ · ε^(−7/2)) (Cutkosky–Mehta, [ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html), Theorem 3; also Fang–Lin–Zhang 2019 up to logarithms).
- **New here: the sharp parameter dependence for third-order smoothness.** The budget above has the dependence Δσ²∛L₃ · ε^(−10/3) in every parameter, with no logarithm, and it is one algorithm whose bound is the minimum of the three regimes. This is exactly the first-order case of the lower-bound expression of Arjevani–Carmon–Duchi–Foster–Sekhari–Sridharan, [COLT 2020](https://proceedings.mlr.press/v125/arjevani20a.html) ([arXiv:2006.13476](https://arxiv.org/abs/2006.13476)), Theorem 3 with p = 3 and no higher-order stochastic derivatives. He's bound is degree 10/3 in the lumped constant M₃, so for example it scales as σ^(20/3) and Δ^(10/3) instead of σ² and Δ. The proof is a tuned-constant version of the He / Cutkosky–Mehta recursion; the mathematical novelty of this half is therefore modest. The pair, and the lower bound against all randomized algorithms, are the contribution; see the [lower-bound note](ThirdOrderSmoothStochasticLowerBound.md).
- **Only p = 3.** Prior art (He, Theorem 4) covers every p ≥ 2 up to logarithms and constants. This repository result treats p = 3 only.

## Setup

[StochasticThirdOrderSmoothNonconvex](../Setups/StochasticThirdOrderSmoothNonconvex.lean) covers the following.

- **Space.** E is any finite-dimensional real inner-product space with its Borel σ-algebra. Ω is any measurable sample space.
- **Objective class.** f : E → ℝ is C³, with
  - ‖∇f(x) − ∇f(y)‖ ≤ L₁‖x − y‖,
  - ‖∇²f(x) − ∇²f(y)‖ ≤ L₂‖x − y‖ (operator norm),
  - ‖∇³f(x) − ∇³f(y)‖ ≤ L₃‖x − y‖ (operator norm of the bilinear-map-valued derivative),
  - f(x₀) − f(x) ≤ Δ for every x.

  This is the class F₃(Δ, L₁, L₂, L₃) of Arjevani et al. 2020, §2, and of Carmon–Duchi–Hinder–Sidford, "Lower bounds for finding stationary points I/II". There is no convexity, no bounded domain and no restriction on the dimension.
- **Role of L₂.** A function with L₁-Lipschitz gradient and L₃-Lipschitz third derivative has a Lipschitz Hessian with a constant of order √(L₁L₃), for which the term √(L₂/ε) is never the minimum. So an instance described only by (L₁, L₃), as in He's Assumptions 1–2, is covered by supplying such an L₂; this interpolation fact is standard and is not formalized here. Keeping L₂ as a separate parameter makes the bound contain the Hessian-Lipschitz rate of Cutkosky–Mehta as the case L₃ → ∞.
- **Oracle.** One call at a point x returns g(x, ξₖ), with ξₖ IID. (x, ξ) ↦ g(x, ξ) is jointly measurable, E g(x, ξ) = ∇f(x) and E‖g(x, ξ) − ∇f(x)‖² ≤ σ². No mean-squared smoothness, no Hessian-vector products, and no two queries with the same sample.
- **Public information.** L₁, L₂, L₃, σ, Δ, ε, x₀ and the spaces.
- **Accuracy criterion.** Integrability of ‖∇f(x̂)‖ and E‖∇f(x̂)‖ ≤ ε, under the product of the algorithm's seed law and the oracle's law.
- **Valid parameters.** L₁, L₂, L₃, ε > 0 and σ, Δ ≥ 0.

A nonlinear, nonconvex family in the class with interacting coordinates: f(x) = Σᵢ cos(xᵢ − xᵢ₊₁) + Σᵢ log cosh(xᵢ) on ℝᵈ. Every coordinate enters at most three terms and cos and log cosh have bounded derivatives up to order four, so L₁, L₂ and L₃ are bounded by absolute constants for every d (the gap Δ grows linearly with d). For general smooth losses, for example networks with tanh or softplus units and bounded weights, the class still applies, but L₁, L₂, L₃ are instance constants that can depend on the dimension and on the weights; no dimension-free claim is made for them. The lower-bound note gives the hard family explicitly.

## Algorithm and cost

[LookaheadMomentum](../Algorithms/LookaheadMomentum.lean), with γ ∈ (0, 1], step η, initial batch n₀ and horizon T:

1. The algorithm seed is an index τ uniform on {0, …, T}.
2. m₀ is the average of n₀ fresh samples at x₀.
3. For t = 0, …, τ − 1:
   - x_{t+1} = x_t − η·m_t/‖m_t‖ (no move if m_t = 0), and d = x_{t+1} − x_t;
   - query one fresh sample at each of the two lookahead points x_{t+1} + ((1−γ)/γ)·d and x_{t+1} + ((2−γ)/γ)·d, with replies g₁ and g₂;
   - m_{t+1} = ((1−γ)(2−γ)/2)·m_t + γ(2−γ)·g₁ − (γ(1−γ)/2)·g₂.
4. Output x_τ. Remaining budget is spent on ignored queries.

The tuning in [LookaheadMomentumTuning](../Proofs/LookaheadMomentumTuning.lean) is

    γ = ε²/(ε² + 300σ²),   r = max{ ε/(32L₁), √(ε/(40L₂)), ∛(ε/(56L₃)) },
    η = min{ γr, ε/(2L₁) },   n₀ = ⌈1/γ⌉,   T = ⌈5Δ/(ηε)⌉.

A run with index τ uses n₀ + 2τ ≤ n₀ + 2T calls. `tuned_calls` proves n₀ + 2T ≤ ⌈100000(1 + σ²/ε² + L₁Δ/ε² + Δσ²M/ε³)⌉. Every oracle call is counted, including the initial batch.

## Proof

**Three-point cancellation ([LookaheadMomentumTaylor](../Proofs/LookaheadMomentumTaylor.lean)).** Write the weights as w = (κ, θ₁, θ₂) = ((1−γ)(2−γ)/2, γ(2−γ), −γ(1−γ)/2) and the positions along d as s = (−1, (1−γ)/γ, (2−γ)/γ). Then Σw = 1, Σ wᵢsᵢ = 0 and Σ wᵢsᵢ² = 0. Hence, in the drift

    κ(∇f(x_t) − ∇f(x_{t+1})) + θ₁(∇f(z₁) − ∇f(x_{t+1})) + θ₂(∇f(z₂) − ∇f(x_{t+1})),

the Hessian term and the third-derivative term of the Taylor expansion at x_{t+1} cancel exactly, for any path, and only remainders are left (`three_point_first`, `three_point_second`, `three_point_third`). With ‖d‖ ≤ η this gives

    ‖drift‖ ≤ min{ 4L₁η, 5L₂η²/γ, 7L₃η³/γ² }

(`coeff_first`, `coeff_second`, `coeff_third`, `drift_le`). The Taylor remainders ‖∇f(x+h) − ∇f(x) − ∇²f(x)h‖ ≤ L₂‖h‖² and ‖∇f(x+h) − ∇f(x) − ∇²f(x)h − ½∇³f(x)[h,h]‖ ≤ L₃‖h‖³ are proved along the segment from the Lipschitz conditions, with crude constants.

**Error split ([LookaheadMomentumMoments](../Proofs/LookaheadMomentumMoments.lean)).** m_t − ∇f(x_t) = noise_t + bias_t. The bias obeys bias_{t+1} = κ·bias_t + drift, so ‖bias_t‖ ≤ drift/(1 − κ) ≤ ε/8 by the choice of η (`bias_bound`). The noise is a martingale-type sum; each step adds two independent fresh samples with weights θ₁, θ₂, so

    E‖noise_{t+1}‖² ≤ κ²·E‖noise_t‖² + (θ₁² + θ₂²)σ²,   and   E‖noise_t‖² ≤ σ²/n₀ + 5γσ²  for all t

(`noise_succ_moment`, `noise_moment`). The fresh-sample step integrates out one coordinate of the IID stream at a time; there is no a priori integrability assumption on the iterates.

**Descent and averaging ([LookaheadMomentumMain](../Proofs/LookaheadMomentumMain.lean)).** For a normalized step, f(x_{t+1}) ≤ f(x_t) − η‖∇f(x_t)‖ + 2η‖m_t − ∇f(x_t)‖ + L₁η²/2 (`normalized_descent`). Summing, using 2u ≤ (10/ε)u² + ε/10 for the noise, and averaging over the uniform index gives

    E‖∇f(x_τ)‖ ≤ Δ/(η(T+1)) + (10/ε)(σ²/n₀ + 5γσ²) + ε/10 + ε/4 + ε/4 ≤ ε

(`path_sum`, `expected_bound`). The trajectory is identified with the template execution in [LookaheadMomentumRun](../Proofs/LookaheadMomentumRun.lean) (`execute_eq`).

## Scope, limits and the tight regime

- **Tight regime and the explicit constant.** Write Y = Δ·M·(1 + σ²/ε²)/ε. On the valid set of the lower setup (Δ·M ≥ 2⁷⁰ε and the dimension condition) and when L₁/ε ≤ M·(1 + σ²/ε²) (in particular when σ²·M ≥ L₁ε), the upper budget is at most 10⁵·(2 + 2⁻⁷⁰)·Y + 1 and the lower budget is at least Y/2¹⁷⁴ − 1. So the two budgets differ by a factor of about 2·10⁵·2¹⁷⁴ ≈ 2¹⁹² once Y ≥ 2¹⁷⁵. This holds for every fixed σ > 0 once ε is small, and there the complexity is Θ((Δσ²/ε³)·M). The constant is universal but astronomically large; the result is a statement about rates, not about practical constants.
- **Unmatched low-noise term.** The term L₁Δ/ε² is not matched by the lower bound. For σ → 0 the true complexity is the deterministic one, where accelerated methods reach ε^(−7/4) under a Lipschitz Hessian and ε^(−5/3) under a Lipschitz third derivative, with matching lower bounds by Zhou ([arXiv:2606.05438](https://arxiv.org/abs/2606.05438)) and, for randomized algorithms, by [arXiv:2610.00245](https://arxiv.org/abs/2610.00245) (Lipschitz Hessian, ε^(−7/4)) and [arXiv:2610.17074](https://arxiv.org/abs/2610.17074) (orders p ≥ 3, ε^(−5/3)). These are exact-oracle results. A bound of the form ε^(−5/3) + σ²ε^(−10/3) is not attempted here; for p = 2 the analogous unified bound is due to Patitucci–Jiang–Mokhtari ([arXiv:2510.03167](https://arxiv.org/abs/2510.03167)).
- **Expected accuracy only.** The guarantee is in expectation for a uniformly sampled iterate. No high-probability statement is made.
- **Known parameters.** The step sizes use L₁, L₂, L₃, σ, Δ and ε. He's schedules are parameter-free; that feature is not reproduced.
- **Constants.** The constants 100000 and 2¹⁷⁴ are not optimized; their product is the ≈ 2¹⁹² gap quoted above. The large lower-bound constant comes from the reused smooth chain construction.
- **Requirement check.** The task asked for an almost tight upper and lower bound for an important, established setup, expressed with `Template` and `TemplateLowerBound`, reusing techniques where convenient. The setup is the standard stochastic nonconvex first-order model with higher-order smoothness; this file gives the `Convergence` half and the companion file the `NonConvergence` half; no open pull request of the repository treats this setup. The high-dimensional lower-bound setup is included in this setup by [ThirdOrderSmoothInclusion](../Proofs/ThirdOrderSmoothInclusion.lean), with the same admissibility and success predicates.
