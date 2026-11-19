# Minibatch extragradient for stochastic weak-Minty variational inequalities

The [main theorem](StochasticWeakMintyExtragradient.lean) is the upper half of a tight pair. With unbiased, bounded-variance stochastic oracles, minibatch extragradient with a uniformly random stopping index finds a point with E‖F(x̂)‖ ≤ ε using at most

    ⌈ 2¹⁹ (1 + L²R²/ε²) (1 + σ²/ε²) ⌉   oracle calls,

for L-Lipschitz operators with a weak Minty solution (ρ ≤ 1/(20L)), in any separable real Hilbert space.

The companion [lower theorem](StochasticWeakMintyLowerBound.lean) shows that ⌊L²R²(ε² + σ²)/(2¹⁹ε⁴)⌋ calls do not suffice, for every randomized algorithm, in high dimension. Together, the stochastic weak-Minty residual complexity is Θ((L²R²/ε²)(1 + σ²/ε²)) up to a universal constant. The contribution, the literature comparison and the scope are discussed in the [lower-bound note](StochasticWeakMintyLowerBound.md). This note documents the upper half.

## Setup

[StochasticWeakMinty](../Setups/StochasticWeakMinty.lean) covers the following.

- **Space.** E is any complete real inner-product space with its Borel σ-algebra, second countable. Ω is any measurable sample space.
- **Instance and oracle.** An instance is F : E → E. The oracle answers g(x, ξₖ) at the k-th call, where ξₖ are IID with law μ under the oracle's seed law.
- **Assumptions.**
  - (x, ξ) ↦ g(x, ξ) is jointly measurable.
  - E g(x, ξ) = F(x) and E‖g(x, ξ) − F(x)‖² ≤ σ², with the integrability these need. These are standard stochastic-VI assumptions; compare Juditsky, Nemirovski and Tauvel, and DDJ'21 §4.
  - F is L-Lipschitz.
  - There is x⋆ with F(x⋆) = 0, ‖x⋆ − x₀‖ ≤ R, and ⟨F(x), x − x⋆⟩ ≥ −ρ‖F(x)‖² for every x, where 0 ≤ ρ ≤ 1/(20L). This is the weak Minty condition of Diakonikolas–Daskalakis–Jordan ([AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), Assumption 1). Our ρ is their ρ/2.
- **Public information.** L, ρ, σ, R, ε, x₀ and the space are public. The algorithm uses L, σ, R, ε and x₀, but not ρ beyond the validity range.
- **Accuracy criterion.** Integrability of ‖F(x̂)‖ and E‖F(x̂)‖ ≤ ε, under the product of the algorithm's seed law and the oracle's seed law.

## Algorithm and cost

[MinibatchExtragradient](../Algorithms/MinibatchExtragradient.lean) uses step size γ = 1/(2L), batch size b = ⌈2048σ²/ε²⌉ + 1, and K = ⌈128L²R²/ε²⌉.

1. The algorithm seed is an index ι uniform on {0, …, K}.
2. Starting from x₀, perform ι extragradient steps:
   - x̄ = x − γ·(mean of b fresh samples at x);
   - x⁺ = x − γ·(mean of b fresh samples at x̄).
3. Then compute one more extrapolation x̄_ι from b fresh samples, and output it.

The run with index ι uses b + 2bι ≤ b(2K + 1) calls. After that the plan is finished and further oracle replies are ignored.

[`stopLen_le_budget`](../Proofs/MinibatchExtragradientRun.lean) proves b(2K + 1) ≤ (2048σ²/ε² + 2)(256L²R²/ε² + 3) ≤ 2¹⁹(1 + L²R²/ε²)(1 + σ²/ε²). Every oracle call is counted.

## Proof

The proof is in [MinibatchExtragradientStep](../Proofs/MinibatchExtragradientStep.lean) and [MinibatchExtragradientRun](../Proofs/MinibatchExtragradientRun.lean).

**Pathwise step (`pathwise`).** Let e₁ and e₂ be the batch errors at x and x̄. With Lγ = 1/2 and ρ ≤ γ/10,

    ‖x⁺ − x⋆‖² + (γ²/11)‖F(x̄)‖² ≤ ‖x − x⋆‖² + 26γ²(‖e₁‖² + ‖e₂‖²) − 2γ⟨x̄ − x⋆, e₂⟩.

It follows from the extragradient identity, the weak Minty inequality at x̄, Lipschitz continuity, and a scalar inequality (`scalar_key`).

**One-step expectation (`step_expect`).**
- The second batch is fresh, so the cross term averages to zero (`batch_lintegral_affine`).
- Each batch error has second moment at most σ²/b (`batch_lintegral_sq`, reused from the repository's stochastic-cohypomonotone proof).
- This gives E[‖x⁺ − x⋆‖² + (γ²/11)‖F(x̄)‖²] ≤ ‖x − x⋆‖² + 52γ²σ²/b.
- Expectations are lower Lebesgue integrals over the IID sample stream. This avoids any a priori integrability assumption on the iterates.

**Recursion (`residualSum_bound`).** By induction on the number of steps, splitting the stream after the first 2b samples (`lintegral_split`),

    (γ²/11) Σ_{ι ≤ K} E‖F(x̄_ι)‖² ≤ ‖x₀ − x⋆‖² + (K + 1)·52γ²σ²/b.

**Output and conclusion (`success`).**
- Averaging over the uniform index gives E‖F(x̂)‖² ≤ 44L²R²/(K+1) + 572σ²/b ≤ ε².
- Jensen's inequality (`enn_l1_of_l2`) then gives integrability and E‖F(x̂)‖ ≤ ε.

## Relation to prior work

- The rate O((L²R²/ε²)(1 + σ²/ε²)) matches DDJ'21, Theorem 4.5(i): EG+ with increasing batches, criterion E‖F̃(u)‖² ≤ ε² on the stochastic estimate, ρ below 1/(8√2L).
- Our variant differs in four ways:
  - it uses a constant batch;
  - it uses a uniformly random output index;
  - it has its own explicit constants;
  - it uses the residual of the mean operator directly.

  It is a self-contained proof under exactly this setup, not a formalization of DDJ's theorem.
- The admissible range ρ ≤ 1/(20L) is narrower than the wider weak-Minty ranges handled with bias correction by Pethick et al., ICLR 2023 ([arXiv:2302.09029](https://arxiv.org/abs/2302.09029)). Their method also needs Lipschitz-in-mean oracles.
- The upper bound is not claimed as new. It closes the pair with the new lower bound.

The lower bound already holds at ρ = 0, so the pair is tight on the whole stated range. The high-dimensional lower-bound setup is included in this setup by [StochasticWeakMintyInclusion](../Proofs/StochasticWeakMintyInclusion.lean).
