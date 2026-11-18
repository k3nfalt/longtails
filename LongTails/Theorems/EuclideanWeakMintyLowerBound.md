# Weak-Minty variational inequalities cannot be accelerated

The [main theorem](EuclideanWeakMintyLowerBound.lean) is a lower bound. Any first-order method needs order (LR/ε)² operator calls to find an ε-residual point of a Lipschitz operator with a Minty solution. This holds for randomized methods and in expectation, once the dimension is large enough.

The extragradient bound in the companion [upper theorem](EuclideanWeakMintyExtragradient.lean) uses O(L²R²/ε²) calls on the same [setup](../Setups/EuclideanWeakMinty.lean). Together the two results settle the first-order oracle complexity of weak-Minty problems, for deterministic and randomized algorithms, up to a universal constant: it is Θ(L²R²/ε²) in high dimension.

This answers, in the negative, an open question about acceleration under weak Minty solutions. Böhm states it in [arXiv:2201.12247](https://arxiv.org/abs/2201.12247) (TMLR 2023, discussion of negative comonotonicity): "It is an open question whether such an acceleration is possible in the more general setting of weak Minty solutions." It also confirms the p=1 case of a conjecture of Lin and Jordan, [arXiv:2205.03202v7](https://arxiv.org/abs/2205.03202) (discussion after their main results). They write: "We would be very surprised if the optimal complexity bound for the monotone setting can be achieved when only the Minty condition holds. Even for the case of p = 1, we are not aware of any relevant supporting evidence." Their paper concerns constrained VIs. The confirmation here is for the unconstrained residual criterion.

## Setup

The [setup](../Setups/EuclideanWeakMinty.lean) is the Euclidean case of the weak-Minty class of [Diakonikolas, Daskalakis and Jordan (AISTATS 2021)](https://proceedings.mlr.press/v130/diakonikolas21a.html), Assumption 1. The parameters are d, L, ρ, x₀, R and ε, and all of them are public: the algorithm may use every one. An instance is an operator F : ℝᵈ → ℝᵈ with:

- exact oracle answers F(x) at every query;
- ‖F(x) − F(y)‖ ≤ L‖x − y‖;
- a point x* with F(x*) = 0, ‖x* − x₀‖ ≤ R, and ⟨F(x), x − x*⟩ ≥ −ρ‖F(x)‖² for every x.

The accuracy criterion is the expected residual, E‖F(x̂)‖ ≤ ε, together with integrability of the returned point's residual.

The validity conditions are:

- L > 0, ε > 0, and 0 ≤ ρ ≤ 1/(20L);
- the nondegeneracy condition 28ε ≤ LR, without which x₀ itself can already be accurate;
- d ≥ 257.

Here ρ is DDJ's ρ/2. The bound ρ ≤ 1/(20L) only serves the upper theorem. The lower bound already holds at ρ = 0, the classical Minty condition, and hence for every ρ ≥ 0. There is no `allowedAlgorithm` restriction.

## Result

With m = min{(LR/(28ε))², (d/257)^{1/3}}, the theorem proves `NonConvergence` for the budget

    ⌊m⌋₊ − 1 operator calls.

Fix any valid parameters, any algorithm (it may be randomized), and any number of calls N up to this budget, including 0. Then there is an admissible instance on which the algorithm's expected residual exceeds ε, or the residual is not integrable.

The instance depends on the algorithm and on N, never on the algorithm's realized seed. The oracle is deterministic.

When d ≥ 257(LR/(28ε))⁶, the budget is ⌊(LR/(28ε))²⌋₊ − 1. That is a constant fraction of the upper budget 2 + 2⌈200L²R²/ε²⌉, so in this regime the bounds match up to a universal constant and no logarithm is lost.

## Hard instance

The construction is in [MintyChainGeometry](../Proofs/MintyChainGeometry.lean). It uses K = N + 1 hidden coordinates π(0), …, π(K−1), with κ = L/6, r = 28ε/L and u = x − x₀. Write clip_r for clamping to [−r, r]. The chain operator is

    G(u)_{π(j)} = a_j(u) · clip_r(u_{π(j)} − r),
    a_0 = κ,   a_j = κ · clamp(4u_{π(j−1)}/r − 1, 0, 1),

with all other coordinates zero. The activation a_j vanishes on the dead zone u_{π(j−1)} ≤ r/4 and equals κ once u_{π(j−1)} ≥ r/2.

1. **Minty holds term by term.** Let x* = x₀ + r Σ_j e_{π(j)}. Then ⟨G(u), u − (x* − x₀)⟩ = Σ_j a_j clip_r(y_j − r)(y_j − r) ≥ 0, where y_j = u_{π(j)}.
2. **Lipschitz.** G is 5κ-Lipschitz, since every coordinate is a bounded, Lipschitz activation times a bounded, 1-Lipschitz clip along a bidiagonal pattern.
3. **Residual floor.** If some y_j ≤ r/2, then induction along the chain gives ‖G(u)‖ ≥ κr/2. The first coordinate that leaves (r/2, 3r/2) has full activation.
4. **Wall.** The operator actually used is F(x) = G(P(u)) + κ(u − P(u)), where P is the projection onto the ball of radius B = 2r√K. It is 6κ = L-Lipschitz, since the projection and its residual are both nonexpansive. Minty survives: in the outer region the wall term contributes at least κt²B², which dominates the chain's worst term −κt²r²/4. The residual floor also survives, as ‖F(x)‖² ≥ ¾‖G(P(u))‖². Every reply is therefore a function of G at a point of norm at most B.
5. **Sizes.** ‖x* − x₀‖ = r√K ≤ R exactly when K ≤ (LR/(28ε))². With these constants the residual floor is at least 2ε.

The operator is not monotone. It is not ρ-comonotone for any ρ either, because the local Jacobian contains a block [[0, 0], [±4κ, a]]. This is consistent with the Θ(LR/ε) rate known under comonotonicity.

**Why the rate is (LR/ε)² rather than LR/ε.** The Minty condition lets the chain have K links, each of length ε/L, for a total distance ε√K/L. Monotone operators admit only about LR/ε useful links (Yoon–Ryu), but the Minty condition only constrains the angle between F(x) and x − x*. Linear (affine) Minty operators are monotone, so no linear or quadratic instance can exhibit this gap. The nonlinear coupling of the activation and the clip is essential.

## Randomized hiding

The hiding argument is in [MintyChainHiding](../Proofs/MintyChainHiding.lean) and [MintyChainLowerBound](../Proofs/MintyChainLowerBound.lean). The hidden coordinates form a uniformly random injective word of length K over Fin d. Before step t, a simulated run reveals only links 0, …, t; it is the repository's prefix-simulation pattern.

Each projected query has at most B²/(r/4)² = 64K coordinates of magnitude above r/4. The existing counting lemma `prefix_family_bad_count_bound` bounds the fraction of words for which any of the N queries, or the output, hits a later hidden coordinate. With D = 256K³ ≤ d − K, that fraction is at most 1/4.

On every other word the true run coincides with the simulated one, and the output's last hidden coordinate stays in the dead zone. Its residual is then at least 2ε, so the average of E‖F(x̂)‖ over words is at least 1.5ε. Some fixed word therefore fails. The output is counted as an extra observation, and the argument covers N = 0.

## Relation to prior work

| Result | Class / oracle | Guarantee |
|---|---|---|
| [Yoon and Ryu, ICML 2021](https://proceedings.mlr.press/v139/yoon21d.html), Thm. 3 | monotone, deterministic span methods | lower bound Ω(LR/ε) for ‖F‖ ≤ ε; the only previously applicable lower bound for weak Minty |
| [Lee and Kim, NeurIPS 2021](https://arxiv.org/abs/2106.02326), Thm. 4.1 | ρ-comonotone, ρ > −1/(2L) | O(LR/ε) (FEG) |
| [Diakonikolas, Daskalakis and Jordan, AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), Thm. 3.2 | weak Minty, ρ < 1/(8L) | EG+: min‖F‖² ≤ 2L‖u₀−u*‖²/((k+1)(1/(4L)−ρ)), i.e. O(L²R²/ε²) |
| [Pethick et al., ICLR 2022](https://arxiv.org/abs/2302.09831); [Pethick, Mavrothalassitis and Cevher, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf) | weak Minty, larger ρ ranges | O(1/ε²) residual; lower bounds only on the admissible ρ range, not on complexity |
| [Anagnostides et al., arXiv:2504.03432v4](https://arxiv.org/abs/2504.03432), §6.2 | Minty VIs, low dimension | d·polylog(1/ε)-type algorithms; lower bounds for computing MVI solutions, not residuals |
| this theorem | weak Minty (already ρ = 0), randomized algorithms, expected residual | Ω((LR/ε)²) for d ≳ (LR/ε)⁶ |

**Searches.** Novelty was checked on 14 November 2026 against:

- arXiv abstracts for "weak Minty", "Minty", "star-monotone", "pseudo-monotone" and "quasi-monotone", each combined with "lower bound";
- the latest versions of the papers above;
- [Alacaoglu, Kim and Wright, arXiv:2402.05071v3](https://arxiv.org/abs/2402.05071) and the Tran-Dinh survey [arXiv:2409.16859](https://arxiv.org/abs/2409.16859);
- Böhm's and Lin–Jordan's statements of the open question.

None of these sources contains an Ω(ε⁻²) residual lower bound for Minty or weak-Minty operators, or a faster method. Most 2026 sources are unrefereed preprints.

## Scope requirement

The setup is the standard, widely used weak-Minty class. The upper bound is DDJ's rate, formalized here through the repository's extragradient analysis. The lower bound is new, and the pair closes the problem up to a universal constant, with no logarithm, in the stated high-dimensional regime.

## Limitations

- **Dimension.** The lower bound needs dimension. In fixed dimension, the Minty halfspaces ⟨F(x), x* − x⟩ ≤ ρ‖F(x)‖² support cutting-plane methods with O(d log(LR/ε)) calls, so some dimension condition is unavoidable. The cube-root exponent in (d/257)^{1/3} is an artifact of the union bound.
- **Constants.** They are not optimized: about 1.3·10⁵ separates the two budgets.
- **Oracle model.** The bound is for exact operator oracles and the residual criterion. Stochastic, higher-order, constrained and min-max-structured versions are not formalized. The chain gives Θ(ε^{−2/p}) for p-th order Minty problems and Ω(σ²L²R²/ε⁴) under bounded variance on paper only; these are not claimed here.
- **Instance structure.** The hard operator is a general Lipschitz VI operator, not the saddle field of an explicit min-max objective. This matches how Böhm and DDJ pose the question.
