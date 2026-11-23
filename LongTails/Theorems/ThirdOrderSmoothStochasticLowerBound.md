# Lower bound for stochastic gradient methods under third-order smoothness

Let M = min{ L₁/ε, √(L₂/ε), ∛(L₃/ε) }. The [main theorem](ThirdOrderSmoothStochasticLowerBound.lean) proves that for **every randomized algorithm** and every budget

    N ≤ ⌊ Δ · M · (1 + σ²/ε²) / (2¹⁷⁴ ε) ⌋

there are a C³ objective with L₁-Lipschitz gradient, L₂-Lipschitz Hessian and L₃-Lipschitz third derivative, initial gap at most Δ, and an unbiased single-query stochastic gradient oracle with variance at most σ², on which the algorithm's output has E‖∇f(x̂)‖ > ε. The instance may depend on the algorithm and on N; it is fixed before the algorithm's seed and the oracle's samples are drawn. The statement covers N = 0 and the stated budget itself.

Together with the [upper theorem](ThirdOrderSmoothStochasticUpperBound.lean), whose budget is ⌈100000(1 + σ²/ε² + L₁Δ/ε² + Δσ²M/ε³)⌉, this determines the oracle complexity of stochastic first-order optimization under third-order smoothness in the noise-dominated regime, up to a universal constant and without logarithms:

    Θ( (Δσ²/ε³) · min{ L₁/ε, √(L₂/ε), ∛(L₃/ε) } ),   i.e.   Θ(Δσ²∛L₃ · ε^(−10/3))  for small ε.

## The question and the prior state

The model is the standard one for nonconvex stochastic optimization: unbiased stochastic gradients with bounded variance (Ghadimi–Lan 2013; Arjevani–Carmon–Duchi–Foster–Srebro–Woodworth, [Math. Program. 2023](https://doi.org/10.1007/s10107-022-01822-7), [arXiv:1912.02365](https://arxiv.org/abs/1912.02365)), with the nested higher-order smoothness class F_p(Δ, L₁, …, L_p) of Carmon–Duchi–Hinder–Sidford and Arjevani et al. 2020. No mean-squared smoothness is assumed and each call returns one gradient at one point with a fresh sample.

- **Lower bounds before this result.**
  - Arjevani et al. 2019, Theorem 3: Ω(L₁Δσ²/ε⁴) for all randomized algorithms when only the gradient is Lipschitz. Their §6 lists higher-order smoothness as open.
  - Arjevani–Carmon–Duchi–Foster–Sekhari–Sridharan, [COLT 2020](https://proceedings.mlr.press/v125/arjevani20a.html) ([arXiv:2006.13476](https://arxiv.org/abs/2006.13476)), Theorem 3: for p-th order stochastic oracles with derivative variances σ₁, …, σ_p, the bound Ω(1)·(Δσ₁²/ε³)·min{ min_q (σ_q/σ₁)^(1/(q−1)), min_q' (L_q'/ε)^(1/q') }. With no stochastic higher derivatives (σ_q = ∞ for q ≥ 2) and p = 3 this is Ω((Δσ²/ε³)·M), the same expression as here. **That theorem is proved for zero-respecting algorithms only.** The authors write that they "believe that existing techniques … can strengthen our lower bounds to apply to general randomized algorithms; for brevity, we do not pursue it here."
- **Upper bounds before this result.** O(L₁Δσ²/ε⁴) by SGD; the sharp O(Δσ²√L₂ ε^(−7/2)) by Cutkosky–Mehta ([ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html), Theorem 3); and Õ(ε^(−(3p+1)/p)) for a Lipschitz p-th derivative by He ([arXiv:2412.14488v4](https://arxiv.org/abs/2412.14488), Theorems 2 and 4), with a logarithm and a lumped constant (degree 10/3 in Δ + σ² + L₁ + L₃² for p = 3). He's paper does not discuss lower bounds for higher-order smoothness, and the heavy-tailed follow-up [arXiv:2506.11214v2](https://arxiv.org/abs/2506.11214) does not either. Earlier, Yu–Xu–Gu ([arXiv:1712.06585](https://arxiv.org/abs/1712.06585)) obtained Õ(ε^(−10/3)) for local minima from third-order smoothness, but with individually smooth components and SCSG variance reduction, a different and stronger oracle model in which ε⁻³ is optimal.

So the exponent 10/3 was known from both sides, but only for zero-respecting algorithms on the lower side and only up to logarithms and with non-matching parameter dependence on the upper side.

## What is new

1. **A lower bound against all randomized algorithms for the class F₃ with a first-order stochastic oracle**, with the full three-way minimum and the factor (1 + σ²/ε²). It removes the zero-respecting restriction of Arjevani et al. 2020, Theorem 3, in the case p = 3 without stochastic higher derivatives. In particular it shows that He's ε^(−10/3) rate cannot be improved by any algorithm, and that neither can the Cutkosky–Mehta and SGD rates in their regimes, in one statement.
2. **A matching upper bound with sharp parameter dependence and no logarithm** (companion theorem).
3. **A machine-checked pair** in the repository's `Convergence` / `NonConvergence` templates.

The techniques are established ones: a probabilistic zero-chain with a masked oracle (Arjevani et al. 2019, §3), hiding by a random coordinate embedding with a bounded-query cutoff, and a smooth chain (Carmon et al.). The new work in the proof is making them compatible with a *Lipschitz third derivative* and with *arbitrary* algorithms simultaneously: the hard function, including the cutoff that confines informative queries to a ball, must have Lipschitz derivatives up to order three with constants independent of the chain length and the dimension, and the masked oracle must not leak the next hidden coordinate through any other gradient entry. The result is best described as closing a known gap with known tools; it is not a new lower-bound technique.

## Setup

[HighDimensionalStochasticThirdOrderSmoothNonconvex](../Setups/HighDimensionalStochasticThirdOrderSmoothNonconvex.lean) is the restriction of [StochasticThirdOrderSmoothNonconvex](../Setups/StochasticThirdOrderSmoothNonconvex.lean) to E = ℝᵈ and Ω = ℝ, with the **same admissibility and success predicates** (`toGeneral`). [ThirdOrderSmoothInclusion](../Proofs/ThirdOrderSmoothInclusion.lean) records the inclusion, so the upper theorem applies to every instance of the lower setup.

- **Instances.** C³ functions f : ℝᵈ → ℝ with L₁-, L₂-, L₃-Lipschitz gradient, Hessian and third derivative (operator norms), and f(x₀) − f(x) ≤ Δ for all x. The initial point x₀ is an arbitrary public parameter.
- **Oracle.** g(x, ξₖ) with ξₖ IID, jointly measurable, unbiased, variance at most σ².
- **Algorithms.** Any `OracleTemplate.Algorithm`: arbitrary state, arbitrary measurable seed, adaptive queries anywhere in ℝᵈ. No zero-respecting, span or bounded-query restriction.
- **Failure.** The negation of: ‖∇f(x̂)‖ integrable and E‖∇f(x̂)‖ ≤ ε, under the product of the algorithm's seed law and the oracle's law.
- **Valid parameters.** L₁, L₂, L₃, ε > 0, σ ≥ 0, and
  - 2⁷⁰ε ≤ Δ·M (the problem is not trivially easy; this also forces Δ > 0);
  - d ≥ 2¹⁴⁰(1 + Δ·M·(1 + σ²/ε²)/ε)⁴ (high dimension).

  The regime is nonempty: for any positive L₁, L₂, L₃, ε and any σ ≥ 0, take Δ = 2⁷⁰ε/M and d large. σ = 0 is allowed and then the bound is the noiseless ⌊ΔM/(2¹⁷⁴ε)⌋.

  Two consequences of these thresholds should be read with the theorem.
  - **Where the budget is positive.** The stated budget is at least 1 only when Δ·M·(1 + σ²/ε²)/ε ≥ 2¹⁷⁴. On the part of the valid set below this level the budget is 0 and the theorem only says that an algorithm making no oracle call fails. The threshold 2⁷⁰ in `valid` is what the proof needs; it was not raised to 2¹⁷⁴ because the statement is stronger with the larger valid set.
  - **Size of the dimension.** Since Δ·M/ε ≥ 2⁷⁰, the dimension condition forces d ≥ 2¹⁴⁰·(2⁷⁰)⁴ = 2⁴²⁰ for every valid parameter choice. The result is a high-dimensional worst-case statement.

## The hard instance

All objects are in [ThirdOrderMaskedOracle](../Proofs/ThirdOrderMaskedOracle.lean) and [ThirdOrderLowerParameters](../Proofs/ThirdOrderLowerParameters.lean).

**Unit function.** For an injection π : {0, …, n} → {1, …, d} let yᵢ = w_{π(i)}. The unit hard function is the localized chain already used in the repository for the Hessian-growth lower bound,

    V_π(w) = χ(‖w‖²/R²) · ( −P(y₀) + Σ_{i<n} [ G(−yᵢ)P(−yᵢ₊₁) − G(yᵢ)P(yᵢ₊₁) ] ) + (c/2)‖w‖²,

with P(t) = π/2 + arctan t, a C^{3,1} spline gate G that is 0 on (−∞, 1/10] and 1 on [1/5, ∞), a C^{3,1} radial cutoff χ equal to 1 inside radius R = 2⁶⁰(n+1) and 0 outside 2R, and c = 3√3/4. Its known properties (from [RelativeHessianLocalized](../Proofs/RelativeHessianLocalized.lean)) are V(0) − V(w) ≤ 4(n+1) and ‖∇V(w)‖ ≥ 7/10 whenever some chain coordinate has |yᵢ| ≤ 1/5.

**New smoothness bounds ([ThirdOrderChainLipschitz](../Proofs/ThirdOrderChainLipschitz.lean), [ThirdOrderJetDifference](../Proofs/ThirdOrderJetDifference.lean)).** For every n and d,

    ∇V is 2⁵⁵-Lipschitz,   ∇²V is 2⁵⁶-Lipschitz,   ∇³V is 2⁶⁰-Lipschitz.

The third is the main new estimate. It needs a Leibniz-type bound for the difference of third derivatives of a product (`product_third_diff`), Lipschitz bounds for the third derivative of each ridge factor (`gateThird_lipschitz`, `densityCurvature_lipschitz`), a sparse summation over chain edges that keeps the constant independent of n (`chain_third_lipschitz`), a dimension-free Hessian bound for the chain (`chain_hessian_norm`), and a Lipschitz bound for the third derivative of the radial cutoff (`cutoff_third_lipschitz`). All four bounds hold at every point of ℝᵈ.

**Scaling.** f(x) = a·V_π((x − x₀)/λ) with

    λ = max{ 2⁵⁸ε/L₁, √(2⁵⁹ε/L₂), ∛(2⁶³ε/L₃) },   a = 5ελ,   n + 1 = ⌊Δ/(20ελ)⌋.

One choice of λ meets the three smoothness constraints at once (`smooth_first`, `smooth_second`, `smooth_third`), and 1/λ is within the factor 2⁵⁸ of M (`stepScale_complexity_le`, `one_le_stepScale_complexity`). The gap is a·4(n+1) ≤ Δ, and ‖∇f‖ ≥ 3.5ε while the last chain coordinate is small.

**Masked oracle.** Let the *stage* m of a query be the number of leading chain coordinates up to the last one exceeding 1/20 in absolute value, and let f_r be f with the chain truncated after r edges. Near a query of stage m the function equals f_m, whose gradient depends on π(0), …, π(m) only. The oracle answers

    g(x, ξ) = ∇f_{m−1}(x) + (1{ξ ≤ q}/q) · (∇f(x) − ∇f_{m−1}(x)),   ξ uniform on [0, 1],

so with probability 1 − q the whole edge (m−1, m) is hidden, not just one coordinate. (At stage 0 there is no such edge and nothing is hidden: the first chain coordinate is given away for free.) It is unbiased, and since ‖∇f_m − ∇f_{m−1}‖ ≤ 2⁵¹·5ε everywhere (`secret_bound`), the choice q = s²/(s² + σ²) with s = 5·2⁵¹ε gives variance at most σ² (`variance_le`). For σ = 0 the oracle is exact.

**Hiding and counting ([ThirdOrderMaskedExecution](../Proofs/ThirdOrderMaskedExecution.lean), [ThirdOrderLowerBound](../Proofs/ThirdOrderLowerBound.lean)).** π is uniform over injections and independent of the algorithm. Let ℓ_t = min(n+1, 1 + number of successful coins before step t). A simulated oracle that knows only π(0), …, π(ℓ_t − 1) reproduces the true replies as long as no query inside the ball of radius 2R has a coordinate π(i), i ≥ ℓ_t, larger than 1/20 (`coupling`); outside that ball the reply is c·w for every π. A query of norm at most 2R has at most (2R)²·400 such large coordinates, so a counting argument over π (reused from the repository, `bounded_prefix_bad_count`) bounds the fraction of bad π by 1/8 in the stated dimension (`bad_fraction`). Markov's inequality gives ℓ_N ≤ n with probability at least 7/8 when 8Nq ≤ n (`good_count_fraction`, `budget_reveal`). On the intersection, the output has a small last chain coordinate or lies outside the ball, so ‖∇f(x̂)‖ ≥ 3.5ε, and averaging over π gives E‖∇f(x̂)‖ ≥ 3ε·(7/8)² > ε for some fixed π (`exists_failure`).

## Scope, limits and comparison of the two halves

- **Tight regime and the explicit constant.** Write Y = Δ·M·(1 + σ²/ε²)/ε. On the valid set of this setup, the ratio of the two budgets is bounded by a universal constant exactly when L₁/ε ≲ M·(1 + σ²/ε²). This holds in particular when σ²·M ≥ L₁ε, and also whenever M = L₁/ε. For fixed parameters with σ > 0 it holds once ε is small. Concretely, if L₁/ε ≤ M·(1 + σ²/ε²) then the upper budget is at most 10⁵·(2 + 2⁻⁷⁰)·Y + 1 while the lower budget is at least Y/2¹⁷⁴ − 1, so the ratio is about 2·10⁵·2¹⁷⁴ ≈ 2¹⁹² once Y ≥ 2¹⁷⁵. Outside it the upper bound has the extra term L₁Δ/ε², which is **not matched**: the lower bound then reads only Ω(ΔM/ε), the rate of exact third-order methods, while the best first-order rates without noise are ε^(−7/4) and ε^(−5/3) (deterministic lower bounds by Zhou, [arXiv:2606.05438](https://arxiv.org/abs/2606.05438); randomized ones in [arXiv:2610.00245](https://arxiv.org/abs/2610.00245) and [arXiv:2610.17074](https://arxiv.org/abs/2610.17074); all for exact oracles). The low-noise regime is left open.
- **Only p = 3.** The scaling argument and the masking are not specific to p = 3, and Arjevani et al. 2020 state the zero-respecting bound for all p. The formal result and the new smoothness estimates are for p = 3 only.
- **Dimension.** The dimension requirement is polynomial, d ≳ (ΔM(1 + σ²/ε²)/ε)⁴, with a large constant. Low-dimensional complexity is not addressed.
- **Expected-norm criterion.** Failure is for the expected gradient norm. A constant-probability statement follows from the same proof but is not stated.
- **Constants.** 2¹⁷⁴ is not optimized; it is the product of the inherited constants of the smooth chain (jets bounded by 2²⁴) and the masking and counting losses. Together with the upper constant it gives the ≈ 2¹⁹² gap above.
- **Requirement check.** The setup is an established one (bounded-variance stochastic nonconvex optimization with the F₃ smoothness class); the upper and lower theorems are stated with `Template` and `TemplateLowerBound` on setups with identical predicates; the techniques are reused from the literature and the repository as permitted; and no open pull request of the repository (#229, #228, #227, #223, #215, #4 at the time of writing) treats higher-order smoothness with stochastic gradients.
