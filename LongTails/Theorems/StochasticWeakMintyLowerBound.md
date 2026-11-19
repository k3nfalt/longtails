# Stochastic Minty variational inequalities need (L²R²/ε²)(1 + σ²/ε²) oracle calls

The [main theorem](StochasticWeakMintyLowerBound.lean) is a lower bound for any randomized method that sees only unbiased, bounded-variance stochastic evaluations. To find a point with expected residual E‖F(x̂)‖ ≤ ε, such a method needs

    ⌊ L²R²(ε² + σ²) / (2¹⁹ ε⁴) ⌋   oracle calls,

even on L-Lipschitz operators with a classical Minty solution (ρ = 0), once the dimension is large.

The companion [upper theorem](StochasticWeakMintyExtragradient.lean) shows that minibatch extragradient succeeds with ⌈2¹⁹(1 + L²R²/ε²)(1 + σ²/ε²)⌉ calls on the [general setup](../Setups/StochasticWeakMinty.lean). The lower-bound setup is a restriction of that setup (see "Relation to the upper bound" below). Together, the stochastic oracle complexity of weak-Minty problems is

    Θ( (L²R²/ε²) · (1 + σ²/ε²) )

up to a universal constant, with no logarithmic factor, in the high-dimensional regime. In particular the ε⁻⁴ rate of the stochastic weak-Minty literature cannot be improved under bounded variance alone.

## How this meets the task requirement

The task asked for an almost tight upper and lower bound pair that closes an important, popular setup in Template / TemplateLowerBound terms.

- **Setup.** Stochastic variational inequalities with a weak Minty solution and an unbiased, bounded-variance oracle. This is the setting of:
  - Diakonikolas, Daskalakis and Jordan, [AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html) (arXiv:2011.00364), Assumption 1 and §4;
  - Pethick et al., ICLR 2023 ([arXiv:2302.09029](https://arxiv.org/abs/2302.09029));
  - Böhm, TMLR 2023 (arXiv:2201.12247);
  - Choudhury, Gorbunov and Loizou, [NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/hash/ccf02786d28730e8311676ffa842e216-Abstract.html) (arXiv:2302.14043);
  - Alacaoglu and Kim, ICML 2026 (arXiv:2602.05531).
- **Tightness.** The upper `Convergence` and lower `NonConvergence` budgets differ by the universal factor 2³⁸·(1 + ε²/(L²R²)) ≤ 2³⁹ on the lower-bound regime.
- **Reuse.** The hard instance reuses the repository's deterministic Minty chain ([PR #182](EuclideanWeakMintyLowerBound.md)) and the probability-p masking idea of Arjevani et al. The task explicitly allows reusing prior techniques.

## Setup

[HighDimensionalStochasticWeakMinty](../Setups/HighDimensionalStochasticWeakMinty.lean) is the Euclidean case E = ℝᵈ, with sample space ℝ, of the general setup [StochasticWeakMinty](../Setups/StochasticWeakMinty.lean). An instance is an operator F : ℝᵈ → ℝᵈ, and the oracle answers g(x, ξₖ) at the k-th call. The admissibility conditions are:

- ξ₀, ξ₁, … are IID with law μ under the oracle's own seed law P. These are the samples that the execution actually uses.
- ‖F(x) − F(y)‖ ≤ L‖x − y‖.
- There is a point x⋆ with F(x⋆) = 0, ‖x⋆ − x₀‖ ≤ R, and ⟨F(x), x − x⋆⟩ ≥ −ρ‖F(x)‖² for every x.
- (x, ξ) ↦ g(x, ξ) is jointly measurable. For every x, E g(x, ξ) = F(x) and E‖g(x, ξ) − F(x)‖² ≤ σ², with the integrability these statements need.

The accuracy criterion is integrability of ‖F(x̂)‖ together with E‖F(x̂)‖ ≤ ε, the same criterion as [EuclideanWeakMinty](../Setups/EuclideanWeakMinty.lean).

All parameters d, L, ρ, σ, R, ε, x₀ are public. The lower bound places no `allowedAlgorithm` restriction: every randomized algorithm is covered.

The validity conditions are:

- the general conditions L > 0, 0 ≤ ρ ≤ 1/(20L), σ ≥ 0, R ≥ 0, ε > 0;
- the nondegeneracy condition 2¹⁰ε ≤ LR. Without it, x₀ itself can be accurate. On this regime the budget is at least 2.
- the dimension condition L⁶R⁶(ε² + σ²) ≤ ε⁸ d, that is, d ≥ (LR/ε)⁶(1 + σ²/ε²). This is the hiding argument's sufficient condition and is not claimed to be necessary. The regime is nonempty: for example L = R = 1, ε = 2⁻¹⁰, σ = 0 and d = 2⁸⁰.

The lower bound already holds at ρ = 0, the classical Minty condition, and hence for every ρ ≥ 0.

## Result

For every valid parameter choice, every algorithm (randomized), and every number of calls N ≤ ⌊L²R²(ε² + σ²)/(2¹⁹ε⁴)⌋, including N = 0, there is an admissible instance on which E‖F(x̂)‖ > ε (or the residual is not integrable). The instance depends on the algorithm and on N, never on the algorithm's realized seed.

## Hard instance and proof

**Deterministic part.** This is the dead-zone chain of [MintyChainGeometry](../Proofs/MintyChainGeometry.lean) (PR #182). Let κ = L/6, r = 28ε/L and K = ⌊(LR/(28ε))²⌋ links, and fix hidden coordinates π(0), …, π(K−1). Let v be the projection of u = x − x₀ onto the ball of radius B = 2r√K. The chain is

    G(v)_{π(j)} = a_j(v)·clip_r(v_{π(j)} − r),   a_0 = κ,   a_j = κ·clamp(4v_{π(j−1)}/r − 1, 0, 1),

and the operator is F(x) = G(v) + κ(u − v). It is L-Lipschitz and satisfies the Minty condition at x⋆ = x₀ + rΣe_{π(j)}, with ‖x⋆ − x₀‖² = Kr² ≤ R². Whenever some v_{π(j)} ≤ r/2, the residual satisfies ‖F‖ ≥ 2ε.

**Masked oracle.** This is new for this setting and lives in [StochasticMintyOracle](../Proofs/StochasticMintyOracle.lean).

- Define the stage s(v) as the least index s such that |v_{π(i)}| ≤ r/4 for all i ≥ s. Because of the dead zone, G(v) vanishes on π(i) for every i ≥ s + 1. The frontier is therefore the single component π(s).
- The oracle multiplies only that chain component by coin(ω) = q⁻¹·[ω ≤ q], with ω ~ Unif[0,1] and q = 1/(1 + 9σ²/(196ε²)). The wall term κ(u − v) does not depend on π and is never masked.
- The oracle is unbiased. Its variance is (1/q − 1)·|G_{π(s)}|² ≤ (1/q − 1)(κr)² = σ², since κr = 14ε/3. It is jointly measurable.
- At σ = 0 we get q = 1, which recovers the deterministic chain.

**Hiding.** This lives in [StochasticMintyHiding](../Proofs/StochasticMintyHiding.lean).

- Let the level ℓ_t = min(K, #{u < t : ω_u ≤ q}) be the capped count of coin successes. It is independent of π and of the algorithm.
- A simulated run answers query t using only π(0), …, π(ℓ_{t+1} − 1).
- On the good event, no query or output puts mass above r/4 on an unrevealed coordinate π(i) with i ≥ ℓ_t. On that event the real run equals the simulated run. This is the coupling lemma `reply_eq_simReply`: when the level does not increase, either the coin failed or the chain is already fully revealed.
- For each fixed coin sequence and algorithm seed, the repository's prefix-counting lemma `bounded_prefix_bad_count`, applied with prefix function ℓ, bounds the fraction of bad hidden words by (N+1)·K·64K/(d − K) ≤ 1/8.
- Markov's inequality on the coin count gives P(ℓ_N ≥ K) ≤ Nq/K ≤ 1/8.
- On the remaining event the last chain coordinate is still at most r/4, so ‖F(x̂)‖ ≥ 2ε. Averaging gives E‖F(x̂)‖ ≥ 2ε·(7/8)² > ε for some π. This step is [StochasticMintyLowerBound](../Proofs/StochasticMintyLowerBound.lean).

The parameter arithmetic is in [StochasticMintyParameters](../Proofs/StochasticMintyParameters.lean).

**What is and is not new technically.** The stochastic step adapts the probability-p zero-chain masking of Arjevani, Carmon, Duchi, Foster, Srebro and Woodworth, [Math. Programming 2023](https://arxiv.org/abs/1912.02365), §3. The adaptation has three parts:

- The chain is a non-gradient dead-zone operator behind a ball-projection wall, so the frontier has to be computed on the projected point.
- The activation threshold r/4 must coincide with the hiding threshold.
- The revealed prefix is indexed by a coin count that does not depend on π, rather than by the step count used in PR #182.

We claim novelty for the result, not for the masking technique.

## Comparison with the literature

| Setting and oracle | Best known residual complexity | Lower bound |
|---|---|---|
| Weak Minty / Minty, bounded variance (this setup) | O((L²R²/ε²)(1+σ²/ε²)): DDJ AISTATS'21, Thm 4.5(i), with growing batches; Õ(ε⁻⁴): Pethick ICLR'23, Böhm TMLR'23, CGL NeurIPS'23, Alacaoglu–Kim ICML'26 | **this theorem**: Ω((L²R²/ε²)(1+σ²/ε²)) |
| Weak Minty, deterministic (σ = 0) | O(L²R²/ε²) (EG) | Ω(L²R²/ε²) (repository PR #182) |
| Monotone, bounded variance | Õ(LR/ε + σ²/ε²) ([Chen–Luo, arXiv:2208.05925](https://arxiv.org/abs/2208.05925); repository InertialMonotoneResidual; Ji–Lan–Zhu, arXiv:2609.04188) | Ω(LR/ε) for span-respecting deterministic first-order methods (Yoon–Ryu, ICML 2021); Ω(σ²/ε²) already for the scaled identity F(x) = L(x − c) with an unknown root c, which reduces to estimating a mean from noisy samples. Ji–Lan–Zhu describe the upper bound as optimal up to logarithms. |
| Cohypomonotone, bounded variance | Õ(LR/ε + σ²/ε²) (repository RegularizedProxExtragradientCohypomonotone) | The monotone lower bounds apply, since monotone operators are cohypomonotone. |

The consequences are:

- **The noise price of non-monotonicity.** Under monotonicity or cohypomonotonicity the statistical cost is additive, σ²/ε². Under the Minty condition it is multiplicative, (LR/ε)²·σ²/ε². The extra factor (LR/ε)² cannot be removed.
- **Optimality of the known algorithms.** DDJ's increasing-batch EG+ (Thm 4.5(i)) is optimal up to a constant factor in its bounded-variance class. For the Õ(ε⁻⁴) methods of Böhm and of Choudhury–Gorbunov–Loizou, our bound shows that the ε⁻⁴ exponent cannot be improved under bounded variance. We have not checked their exact dependence on L and R, or every variant of their noise assumptions, so we do not claim constant-factor optimality for them. Alacaoglu–Kim treat constrained VIs whose oracle variance may grow with the iterate. Our unconstrained ℝᵈ instances with bounded variance fall inside their class, so their ε⁻⁴ exponent cannot be improved either.

We found no published or arXiv lower bound for stochastic (weak) Minty VIs. Our searches were targeted rather than exhaustive: keyword searches of ICML/ICLR/NeurIPS proceedings (2024–2026) and of arXiv up to November 2026, plus the reference lists of the papers above. Pethick et al. motivate their work by contrast with minimization, where Arjevani et al. give matching bounds; they do not pose the question formally. The deterministic Ω(L²R²/ε²) bound of PR #182 also appears to be unpublished outside this repository.

## Limitations and scope

- **Lipschitz-in-mean classes.** The hard oracle is discontinuous in x: the frontier jumps. It is not Lipschitz in mean (mean-squared smooth). The bound therefore does **not** apply to the class of Pethick et al. (ICLR 2023, Assumption III), which also assumes Lipschitz-in-mean oracles. Whether variance reduction gives ε⁻³ for weak-Minty VIs under mean-squared smoothness remains open.
- **Dimension.** High dimension is required: d ≥ (LR/ε)⁶(1 + σ²/ε²) suffices. Smaller dimension is not addressed.
- **Accuracy criterion.** The criterion is the expected residual. High-probability guarantees and other criteria are not covered.
- **Higher-order oracles.** p-th order oracles (Lin–Jordan) are not addressed.
- **Constants.** The universal constant gap is 2³⁸–2³⁹.

## Relation to the upper bound

- [StochasticWeakMintyInclusion](../Proofs/StochasticWeakMintyInclusion.lean) proves `Includes StochasticWeakMinty.spec HighDimensionalStochasticWeakMinty.spec`. Admissibility and success are literally those of the general setup at E = ℝᵈ, Ω = ℝ, and validity implies general validity.
- The upper theorem therefore applies verbatim to every instance of this setup.
- The lower budget is ⌊(L²R²/ε²)(1 + σ²/ε²)/2¹⁹⌋ and the upper budget is ⌈2¹⁹(1 + L²R²/ε²)(1 + σ²/ε²)⌉. Since L²R²/ε² ≥ 2²⁰ on the regime, they match up to the universal constant above.
