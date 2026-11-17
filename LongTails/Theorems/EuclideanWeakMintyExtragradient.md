# Extragradient upper bound for Euclidean weak-Minty problems

The [main theorem](EuclideanWeakMintyExtragradient.lean) is the upper half of a matching pair. It shows that an extragradient method finds a point with ‖F(x̂)‖ ≤ ε, deterministically and hence in expectation, using

    2 + 2⌈200L²R²/ε²⌉ operator calls.

This holds for every Lipschitz operator in the [Euclidean weak-Minty setup](../Setups/EuclideanWeakMinty.lean), in any dimension.

The companion [lower bound](EuclideanWeakMintyLowerBound.lean) proves that no algorithm, deterministic or randomized, can reach expected residual ε with fewer than ⌊min{(LR/(28ε))², (d/257)^{1/3}}⌋₊ − 1 calls. The two theorems use the same setup, oracle and accuracy criterion. Together they give the complexity Θ(L²R²/ε²) for d ≥ 257(LR/(28ε))⁶, up to a universal constant. That note explains the new contribution and the literature; this note covers the upper half.

## What is new and what is known

The rate O(L²R²/ε²) is known. EG+ attains it in [Diakonikolas, Daskalakis and Jordan, AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), Theorem 3.2, for ρ < 1/(8L) in our convention. Later methods enlarge the admissible ρ range ([Pethick et al., ICLR 2022](https://arxiv.org/abs/2302.09831); [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf)).

This theorem is not a new rate. It is the formal upper half of the tight characterization, stated on exactly the setup, oracle and expected-residual criterion of the new lower bound.

## Setup, algorithm and output

The setup is described in the lower-bound note. Its key properties are:

- F is L-Lipschitz on ℝᵈ;
- there is a root x* with ‖x* − x₀‖ ≤ R and ⟨F(x), x − x*⟩ ≥ −ρ‖F(x)‖²;
- 0 ≤ ρ ≤ 1/(20L);
- the oracle is exact.

The only conditions this theorem does not use are the dimension condition d ≥ 257 and the nondegeneracy condition 28ε ≤ LR. Both belong to the shared setup because the lower bound needs them.

The [algorithm](../Algorithms/EuclideanWeakMintyExtragradient.lean) is the repository's [non-Euclidean extragradient method](../Algorithms/NonEuclideanExtragradient.lean), specialized to the mirror h = ½‖·‖² with μ = 1. Euclidean replies are passed through the Riesz map v ↦ ⟨v, ·⟩. In this geometry, at base point x it computes

    y = x − F(x)/(2L)   and   x⁺ = x − F(y)/(10L),

which is an EG+ step. It returns the queried base point with the smallest observed residual. Each iteration uses two calls, and the algorithm uses only L, ρ and x₀.

## Proof

The [proof module](../Proofs/EuclideanWeakMintyExtragradientRun.lean) carries out the following steps.

1. It computes the Bregman divergence of h = ½‖·‖² exactly: D_h(u, x) = ½‖u − x‖².
2. It verifies the validity conditions of the repository's [NonEuclideanWeakMinty](../Setups/NonEuclideanWeakMinty.lean) public data.
3. It shows that the Riesz map preserves the Lipschitz and weak-Minty conditions.
4. It proves that executing the wrapped algorithm against the Euclidean oracle produces the same point as the original method run against the dual oracle.
5. It applies the existing guarantee `execute_accuracy` with D = R²/2.

Because the run does not depend on any seed, the residual of the returned point is constant across seeds. It is therefore integrable, and its expectation is at most ε.

## Limitations

- The constant 200 and the restriction ρ ≤ 1/(20L) come from the reused analysis. Sharper EG+ analyses allow larger ρ and smaller constants.
- The theorem does not cover constrained, stochastic, or higher-order oracles.
