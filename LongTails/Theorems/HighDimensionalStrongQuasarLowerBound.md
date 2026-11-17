This result proves the first lower bound for smooth strongly quasar-convex minimization that has the product form γ⁻¹√κ · log(1/ε) of the known accelerated upper bound. It holds for **randomized** gradient methods. Previously, only the two separate terms γ⁻¹√κ and γ^{-1/2}√κ·log(1/ε) had proofs; the product had not been proved for either deterministic or randomized methods. Together with the existing accelerated upper bound, restated in [HighDimensionalStrongQuasarUpperBound](HighDimensionalStrongQuasarUpperBound.lean), the complexity of this class is now determined up to a universal constant factor in the accuracy regime ε ≤ Δ/(10⁶γκ), and up to an O(log κ) factor elsewhere in the stated regime.

## Setup

The [main theorem](HighDimensionalStrongQuasarLowerBound.lean) uses [HighDimensionalStrongQuasar](../Setups/HighDimensionalStrongQuasar.lean). Its admissible instances and success criterion are, verbatim, those of the existing [RelativeGradientStrongQuasar](../Setups/RelativeGradientStrongQuasar.lean) setup at relative error δ = 0, specialized to ℝᵈ:

- f is differentiable with L-Lipschitz gradient.
- The oracle returns the exact gradient ∇f(x) at each query, through a measurable deterministic map.
- f has a global minimizer x⋆ with f(x₀) − f(x⋆) ≤ Δ.
- f is (γ, μ)-strongly quasar-convex with respect to x⋆: for every x,

  γ f(x) + ⟨∇f(x), x⋆ − x⟩ + γμ/2 ‖x⋆ − x‖² ≤ γ f(x⋆).

This is Definition 1 of [Hinder, Sidford and Sohoni, COLT 2020](https://proceedings.mlr.press/v125/hinder20a.html) ([arXiv 1906.11985 v3](https://arxiv.org/abs/1906.11985)). It is also the class used by later work on quasar-convex acceleration and its stochastic variants.

Success means that the actual execution output has an integrable objective gap whose expectation, over the algorithm's seed, is at most ε. All parameters are public: d, L, x₀, μ, γ, Δ and ε.

The numerical conditions in `valid`, with κ = L/μ, are:

- γ ≤ 1/256;
- κ ≥ 870400;
- γ²κ ≥ 4;
- Δ ≥ 1000 γ√κ ε;
- d ≥ (√κ/γ)⁵ · (Δ/(1000γ√κε))³.

They select a parameter regime and a sufficiently large dimension. They do not restrict the admissible objectives beyond the standard class.

## Theorem

Every randomized algorithm with gradient access fails on some admissible instance at every integer budget

**0 ≤ b ≤ ⌊√κ/(8000γ)⌋ · ⌊log₂⌊Δ/(1000γ√κε)⌋⌋ / 2,**

which is Ω(γ⁻¹√κ · log(Δ/(γ√κε))).

- The algorithm may choose arbitrary adaptive query points and an arbitrary output, and may use arbitrary internal randomness. No span, zero-respecting or update-family restriction is imposed.
- The hard instance may depend on the algorithm and the budget, but not on the realized seed.
- The quantifiers are those of `NonConvergence`. In particular, the zero budget is included.
- The bound is nontrivial once Δ ≥ 2000γ√κε, so that the log factor is at least 1. Note that Δ/(γε) ≥ 2000√κ is a stronger condition than the setup's Δ ≥ 1000γ√κε.
- The nonempty regime is witnessed, for example, by L = 10⁷, μ = 1, γ = 1/256, Δ = 1, ε = 10⁻¹⁰ and a sufficiently large d.

## Comparison with the upper bound

The repository's [accelerated method for relative-error strongly quasar-convex functions](AcceleratedRelativeQuasar.lean), at δ = 0, achieves the same expected criterion within ⌈32√κ/γ⌉ · ⌈log₂(1 + 2Δ/(γε))⌉ gradient calls. [HighDimensionalStrongQuasarUpperBound](HighDimensionalStrongQuasarUpperBound.lean) restates this guarantee in the present setup and simplifies its budget. It is a known upper bound, not a new upper-complexity claim. The order γ⁻¹√κ log(1/ε) appears in HSS Theorem 1, with an extra log(γ⁻¹κ) factor from binary search and with function-value queries. Continuized acceleration with this order and no binary search is due to [Wang and Wibisono, ICLR 2023](https://openreview.net/pdf?id=yYbhKqdi7Hz). Their Theorem 2 is a continuized-time expectation bound: its discrete form controls E[exp(c·T_k)·gap] at a random time T_k. Their Corollary 2 is a high-probability bound. The fixed-budget expected-gap version with the stated budget is the repository's own theorem.

Write A = Δ/(γε). The upper logarithm is log₂(1 + 2A); the lower logarithm is ⌊log₂⌊A/(1000√κ)⌋⌋.

- When A ≥ 10⁶κ, that is ε ≤ Δ/(10⁶γκ), we have log(A/(1000√κ)) ≥ ½ log A. Then the upper and lower bounds agree up to a universal constant factor, and the complexity is

  **Θ(γ⁻¹√κ · log(Δ/(γε))).**

  The explicit ratio of upper to lower budget is then at most about 2·10⁶. This comes from the leading constants 32 and 1/16000, plus the factor-two loss in the logarithm. The constants are not optimized.
- In the remaining range, 2000√κ ≤ A < 10⁶κ, the lower logarithm is at least 1. The ratio of the upper to the lower bound is O(log κ).
- For A < 2000√κ, the stated lower budget is zero and the theorem is vacuous.

The upper bound needs neither the dimension condition nor the other `valid` restrictions. They restrict only where the pair is stated.

## What was known

- **[Hinder–Sidford–Sohoni](https://arxiv.org/abs/1906.11985) (v3, COLT 2020).**
  - *Remark 4 (arXiv v3; Remark 5 in the COLT version) states:* "Given any deterministic first-order method, there exists an L-smooth, (γ, µ)-strongly quasar-convex function such that the method requires at least Ω(max{γ⁻¹L^{1/2}µ^{-1/2}, γ⁻¹L^{1/2}µ^{-1/2} log₊(ε⁻¹)}) gradient evaluations to find an ε-optimal point of f."
  - *What its proof establishes:*
    - The first term γ⁻¹√κ, by reduction from the non-strongly quasar-convex Theorem 3.
    - Only γ^{-1/2}√κ log₊(1/ε) for the second term. The proof observes that a (γ, μ)-strongly quasar-convex quadratic is (γμ/2)-strongly convex, and then applies Nesterov's quadratic lower bound.

    Neither argument gives the product γ⁻¹√κ log(1/ε). A strongly convex quadratic cannot exhibit the γ⁻¹ factor at all.
  - *Scope:* HSS state and prove both parts for deterministic methods. We checked the proof text in arXiv v2 and v3 and in the COLT version. Randomized versions of the two *separate* terms follow from known results:
    - γ^{-1/2}√κ log(1/ε). Every L-smooth, (γμ)-strongly convex function is (γ, μ)-strongly quasar-convex, since ⟨∇f(x), x⋆ − x⟩ ≤ f⋆ − f(x) − (γμ/2)‖x − x⋆‖² and γ ≤ 1. Its condition number is κ/γ, so any randomized √κ′·log(1/ε) lower bound for κ′-conditioned smooth strongly convex minimization transfers. An example is the randomized bound Ω(m + √(mκ′)·log(1/ε)) of [Woodworth and Srebro, NeurIPS 2016](https://arxiv.org/abs/1605.08003), in its m = 2 case (Theorem 8), simulating one full-gradient call by two component calls.
    - γ⁻¹√κ: the reduction of Remark 4 applied to a randomized quasar-convex lower bound.

    The product γ⁻¹√κ log(1/ε) had not been proved in either model.
- **Open PR #175 (constrained quasar-convex randomized lower bound).** It concerns the non-strongly quasar-convex class over a constraint set, with rate of order γ⁻¹√(LR²/ε). It makes no strongly quasar-convex claim. A reduction in the style of HSS Remark 4 can at best transfer a γ⁻¹√κ term to the strongly quasar-convex class, not the logarithmic product. No black-box theorem converts a sublinear-class lower bound into a linear-rate γ⁻¹√κ·log(1/ε) lower bound.
- **Strongly convex randomized lower bounds** ([Woodworth and Srebro, NeurIPS 2016](https://arxiv.org/abs/1605.08003)). Their Theorem 8 assumes m ≥ 2; its m = 2 case gives √κ log(1/ε) for full-gradient methods, simulating each full-gradient call by two component calls, with no γ-dependence. Randomized quadratic lower bounds ([Simchowitz, 2018](https://arxiv.org/abs/1807.09386)) give Ω(√κ) at constant accuracy. As explained above, these imply at most γ^{-1/2}√κ log(1/ε) for the quasar class.
- **Recent work.** We surveyed ICML/ICLR 2025–2026, NeurIPS 2024–2025 and arXiv through 14 November 2026. The searches covered quasar-convex lower bounds, strongly quasar-convex complexity, the log(1/ε) term for randomized methods, and follow-ups to HSS. No paper claiming the product lower bound was found, for either deterministic or randomized methods. Some OpenReview pages for NeurIPS 2026 were not accessible; they are not treated as evidence either way.

## Mechanism

The hard function is a long scaled chain, with three ingredients designed so that strong quasar-convexity survives the γ⁻¹ amplification.

1. **Geometric chain with exact KKT.**
   - The target point has coordinates aₚ = q^{p+1} along a hidden ordered set of coordinates, where q = 1 − 1/m and m ≍ √κ/γ.
   - Consecutive coordinates are coupled by a convex dead-zone difference energy H(t) = ½((|t| − θ)₊)², with an anchor 1 − x₁.
   - Each chain coordinate carries a one-dimensional potential βₚE_ρ + μaₚ²ψ(·/aₚ). Its coefficients βₚ are chosen so that the chain's first-order conditions hold exactly at x⋆.
   - Off-chain coordinates carry μ/2‖x‖² only.

   See [StrongQuasarChainObjective](../Proofs/StrongQuasarChainObjective.lean).
2. **Masked quadratic.** ψ(v) = ∫₁ᵛ g(s)(s−1)ds, where g(s) = min(1, max(0, 16|s| − 1)) vanishes near zero. The quadratic reward toward aₚ is therefore switched off on undiscovered coordinates, which keeps the tail of the chain invisible. Where it is active, it supplies the strong-quasar term. See [StrongQuasarChainScalar](../Proofs/StrongQuasarChainScalar.lean).
3. **Sequence-level quasar inequality** ([StrongQuasarChainBlock](../Proofs/StrongQuasarChainBlock.lean), `Regime.chain_nonneg`).
   - SQC reduces to (1−γ)·Σ link Bregman + Σ μ(g(vᵢ) − γ)(Xᵢ − aᵢ)² ≥ 0 for every chain profile.
   - Indices with g < γ ("bad" indices) contribute negatively. They are grouped into maximal runs, and each run is charged to the link Bregman divergences across it, by telescoping and Cauchy–Schwarz, or to good indices inside long runs.
   - The argument is proved under the sufficient condition (42γm)²μ ≤ 1, where μ is the normalized modulus. This condition is why the chain length per e-fold of progress is ≍ √κ/γ, rather than the √κ attainable for convex functions.
   - The inequality is genuinely nonlinear and couples all chain coordinates. Scalar or quadratic examples cannot exhibit it: on quadratics, strong quasar-convexity collapses to strong convexity with modulus γμ/2.

The function is then localized by the repository's exact ramp blend with a radial wall, which preserves SQC through an explicit shell inequality ([StrongQuasarChainLocalized](../Proofs/StrongQuasarChainLocalized.lean)). It is normalized, and its smoothness constant is tracked (≤ 512). Finally it is scaled to the public L, μ, Δ and x₀ ([StrongQuasarChainParameters](../Proofs/StrongQuasarChainParameters.lean), [StrongQuasarChainLowerBound](../Proofs/StrongQuasarChainLowerBound.lean)).

Randomized hardness uses coordinate hiding with a uniformly random ordered coordinate word ([StrongQuasarChainAveraging](../Proofs/StrongQuasarChainAveraging.lean)):

- While the coordinates beyond the discovered prefix are small, the oracle answer depends only on the discovered prefix ([StrongQuasarChainHard](../Proofs/StrongQuasarChainHard.lean), `partialField_prefix`).
- A union bound over the b queries and the output bounds the probability that any of them is large on an undiscovered coordinate.
- Undiscovered coordinates force an expected gap of at least the tail value μ·ψ(0)·Σ_{p ≥ b} aₚ². This value exceeds 2ε throughout the stated budget.
- Outputs outside the localization ball are inaccurate because of the wall.
- The bound is averaged over the finite family of hidden words before a fixed witness is chosen. This gives the `NonConvergence` quantifiers.

## Assumptions and limitations

- **Standard class.** The objective class is exactly smooth (γ, μ)-strongly quasar-convex functions with an exact gradient oracle and an initial-gap bound, as in HSS. No new assumption is added.
- **Regime restrictions.** γ ≤ 1/256 and κ ≥ 870400 are constant-size restrictions coming from the chain inequality. γ²κ ≥ 4, i.e. γ√κ ≥ 2, is used only in `muN_m_le` ([StrongQuasarChainParameters](../Proofs/StrongQuasarChainParameters.lean)). That lemma bounds μₙm ≤ 2 for the normalized modulus μₙ = 8704/κ and chain length m ≍ √κ/γ. This keeps the normalized initial gap (`gapZero_le`) and the hiding-radius ratio (`dimension`) bounded. The condition excludes γ ≲ κ^{-1/2}. That range is a proof restriction, not a claim about the complexity there.
- **Dimension.** The required dimension (√κ/γ)⁵(Δ/(γ√κε))³ is polynomial in √κ/γ and in Δ/ε. Equivalently, it is exponential in bγ/√κ, the number of e-folds of accuracy demanded. No dimension-free or polynomial-in-b statement is claimed.
- **Constants.** Constants (8000, 1000, the powers in the dimension) are not optimized.
- **Log mismatch.** The bounds are tight up to constants only for ε ≤ Δ/(10⁶γκ). Otherwise they are tight up to an O(log κ) factor, and the lower bound is vacuous when Δ/(γε) < 2000√κ.
- **Oracle model.** The oracle is the exact gradient oracle. No lower bound is claimed for the relative-error oracle with δ > 0, or for value-and-gradient oracles with stochastic stopping.

## Scope requirement

The task asked for almost-tight upper and lower bounds for an important, popular setup, closing a problem up to log factors.

- The setup is the standard smooth strongly quasar-convex class.
- The upper bound O(γ⁻¹√κ log(Δ/(γε))) was known, from HSS Theorem 1 (up to a log factor), Wang–Wibisono (ICLR 2023) and the repository's accelerated method. It is restated in the same setup.
- The matching lower bound is new, and is proved for all randomized algorithms.
- Together they determine the complexity up to a constant when ε ≤ Δ/(10⁶γκ), and up to an O(log κ) factor otherwise.
