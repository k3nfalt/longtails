# Stochastic nonconvex–PŁ minimax needs κℓΔ/ε² + κ²ℓΔσ²/ε⁴ gradient calls

The [main theorem](StochasticNonconvexPLLowerBound.lean) is a lower bound for every randomized algorithm that sees only unbiased, bounded-variance stochastic gradients of a smooth minimax objective f(x, y) that is nonconvex in x and Polyak–Łojasiewicz (PŁ) in y. With κ = ℓ/μ, such an algorithm needs

    ⌊ ℓ²Δ / (2⁹⁴ μ ε²) · (1 + ℓσ² / (2⁵⁹ μ ε²)) ⌋   oracle calls

to output a point whose Moreau-envelope stationarity measure satisfies E‖∇Φ_{1/(2ℓ)}(x̂)‖ ≤ ε, where Φ(x) = max_y f(x, y), once the dimension is large.

The companion [upper theorem](StochasticNonconvexPLUpperBound.lean) ([note](StochasticNonconvexPLUpperBound.md)) shows that single-loop Smoothed-AGDA succeeds with 2⌈2⁴⁴ (ℓ²Δ/(με²)) (1 + ℓσ²/(με²))⌉ calls on the [general setup](../Setups/StochasticNonconvexPL.lean), of which the lower-bound setup is a restriction. Together the stochastic gradient complexity of nonconvex–PŁ minimax optimization under this criterion is

    Θ( κℓΔ/ε² + κ²ℓΔσ²/ε⁴ )

up to a universal constant and with no logarithmic factor, in the regime κ ≥ 2⁴⁷, ℓΔ/ε² ≥ 2⁴⁷ and d at least an explicit polynomial in κ, ℓΔ/ε² and σ/ε (see "Validity" below).

## How this meets the task requirement

The task asked for an almost tight upper and lower bound pair that closes an important, popular setup in Template / TemplateLowerBound terms, reusing earlier techniques where convenient.

- **Setup.** Smooth nonconvex–PŁ minimax problems with a stochastic gradient oracle. This is the setting of Nouiehed et al., NeurIPS 2019 ([arXiv:1902.08297](https://arxiv.org/abs/1902.08297)); Yang, Kiyavash and He, NeurIPS 2020 ([arXiv:2002.09621](https://arxiv.org/abs/2002.09621)); Yang, Orvieto, Lucchi and He, AISTATS 2022 ([arXiv:2112.05604](https://arxiv.org/abs/2112.05604)); Pan and Li ([arXiv:2608.26799](https://arxiv.org/abs/2608.26799)); and Ha ([arXiv:2610.07814](https://arxiv.org/abs/2610.07814)). It contains nonconvex–strongly-concave problems.
- **Tightness.** Both budgets have the form c·X·(1 + c′Y) with X = ℓ²Δ/(με²) and Y = ℓσ²/(με²). The `Convergence` budget is at most 2²⁰⁰ times the `NonConvergence` budget for every valid parameter choice of the lower-bound setup, including σ = 0.
- **Reuse.** The upper bound re-derives the Smoothed-AGDA potential analysis already in the repository for two-sided PŁ problems. The lower bound reuses the repository's coordinate-embedding hiding argument and Bernoulli masking pipeline ([ABC noise](AbcNoiseLowerBound.md), [stochastic weak Minty](StochasticWeakMintyLowerBound.md)). The hard function itself is new.

## Setup

[HighDimensionalStochasticNonconvexPL](../Setups/HighDimensionalStochasticNonconvexPL.lean) is the Euclidean case E = F = ℝᵈ, with sample space ℝ, of [StochasticNonconvexPL](../Setups/StochasticNonconvexPL.lean). An instance is a function f : ℝᵈ × ℝᵈ → ℝ. One oracle call at (x, y) returns a pair (G_x, G_y) computed from a fresh sample. Admissibility requires:

- f is differentiable in each block and both partial gradients are jointly ℓ-Lipschitz: ‖g(z) − g(z′)‖ ≤ ℓ(‖x − x′‖ + ‖y − y′‖).
- PŁ in y: 2μ(f(x, y′) − f(x, y)) ≤ ‖∇_y f(x, y)‖² for all x, y, y′.
- For every x the maximum over y is attained, and Φ = max_y f is bounded below.
- The oracle is jointly measurable, unbiased, and E(‖G_x − ∇_x f‖² + ‖G_y − ∇_y f‖²) ≤ σ² at every query. The samples are IID across calls.
- Initialization: 2Φ(x₀) − inf Φ − f(x₀, y₀) + ‖∇_x f(x₀, y₀)‖²/ℓ ≤ Δ. This is the potential gap that the Smoothed-AGDA analysis of Yang et al. actually consumes: a primal gap plus a duality gap plus the initial primal gradient.

No function values are available. All parameters d, ℓ, μ, σ, Δ, ε, x₀, y₀ are public. There is no `allowedAlgorithm` restriction, so every randomized algorithm is covered.

**Accuracy.** The output x̂ must satisfy E[2ℓ·dist(x̂, prox(x̂))] ≤ ε, where prox(x̂) is the set of minimizers of Φ(x) + ℓ‖x − x̂‖². Since Φ is ℓ-weakly convex the minimizer is unique and the quantity is ‖∇Φ_{1/(2ℓ)}(x̂)‖, the near-stationarity measure of Davis and Drusvyatskiy ([arXiv:1803.06523](https://arxiv.org/abs/1803.06523)).

**Validity.** The lower bound holds for parameters satisfying

- μ > 0, μ ≤ ℓ, σ ≥ 0, Δ ≥ 0, ε > 0 (the general conditions);
- 2⁴⁷ μ ≤ ℓ and 2⁴⁷ ε² ≤ ℓΔ (nondegeneracy; under these the budget is at least 1);
- 2⁹⁹ (X(1 + Y) + 1) (ℓΔ/ε²)² (ℓ/μ)³ ≤ d with X, Y as above. This is the hiding argument's sufficient dimension and is not claimed necessary.

The regime is nonempty: for example ℓ = Δ = 1, μ = 2⁻⁴⁷, ε = 2⁻²⁴, σ = 0 and d large.

## Result

For every valid parameter choice, every randomized algorithm, and every number of calls T up to the budget (including T = 0), there is an admissible instance and oracle on which E‖∇Φ_{1/(2ℓ)}(x̂)‖ > ε or the measure is not integrable. The instance depends on the algorithm and on T but never on the algorithm's realized seed.

## Which criterion is closed

The Moreau measure is weaker than ‖∇Φ(x̂)‖. Under the assumptions above Φ is differentiable with ∇Φ(x) = ∇_x f(x, y⋆(x)) (Nouiehed et al. 2019, Lemma A.5), and Φ + ℓ‖· − x̂‖² is ℓ-strongly convex, so ℓ‖x̂ − prox(x̂)‖ ≤ ‖∇Φ(x̂)‖ and hence ‖∇Φ_{1/(2ℓ)}(x̂)‖ ≤ 2‖∇Φ(x̂)‖. This implication is stated here in prose and is not part of the Lean development. A lower bound for the weaker measure is the stronger statement, so the bound above also applies to E‖∇Φ(x̂)‖ ≤ ε/2.

| criterion | upper bound | lower bound |
| --- | --- | --- |
| E‖∇Φ_{1/(2ℓ)}(x̂)‖ ≤ ε | κℓΔ/ε² + κ²ℓΔσ²/ε⁴ ([companion theorem](StochasticNonconvexPLUpperBound.lean)) | same rate (this theorem) |
| E‖∇Φ(x̂)‖ ≤ ε | the same two terms plus a post-processing term: Õ(κ⁵σ²/ε²) in Yang et al. 2022 (Cor. 4.1 with Prop. 2.1(b)); (κ + κ⁴σ²/ε²)·log 2κ in Ha 2026, Prop. E.1, under his initialization condition (E.1) | same two terms (implied by this theorem) |

So the pair is tight for the Moreau criterion. For the gradient-of-Φ criterion the two leading terms are now matched from below, and the additive post-processing term is not addressed here.

## Hard instance

Write N = n + 1 for the number of dual links in a block and M = m + 1 for the number of blocks. The unscaled function on ℝᵈ × ℝᵈ is

    F(x, y) = ‖x‖²/32 + Σ_k h(y_k) + c_y(y)·R(u(x), w(y)) − C(u(x)),

where

- π embeds the K = M(N + 1) chain positions into the d coordinates. Position (i, j) with j < N is the dual coordinate w_{i,j} = y_{π(i,j)} and position (i, N) is the primal coordinate x_{π(i,N)}.
- u_i(x) = c_x(x)·x_{π(i,N)}, where c_x and c_y are smooth radial cut-offs equal to 1 on a ball of radius B_x ≍ √M (resp. B_y ≍ √(MN)) and 0 outside twice the radius.
- h(v) = −(λ/2)v² − ½·max(−v − r₀/2, 0)² with λ = 1/(2048N) is a weak concave quadratic with a one-sided guard, applied to every coordinate of y.
- R = Σ_i ρ(s_i, u_i, w_i) with front s_i = s_max·ψ(u_{i−1}) (block 0 is always on), and the block reward is

      ρ(s, t, w) = Σ_j α_j(s)·gate(w_{j−1}/r_{j−1})·push(w_j/r_j) + α_T(s)·(4 − φ(t))·gate(w_n/r_n),

  with gate ≡ 0 below 1 and ≡ 1 above 2, push increasing and concave on the positive side, φ the usual S-shaped chain profile, scales r_j = max(N^{−1/2}, 2^{−(N−1−j)}), weights ω_j = max(1/N, 4^{−(N−j)}), and r_j² = ω_{j+1}.
- C = Σ_i comp(s_i) with comp(s) = Σ_j α_j(s) + 4α_T(s) ≥ ρ, so the chain part is nonpositive.
- **Staggered amplitudes.** α_j(s) = ω_j·cap(ramp_{ω_j}(s − Σ_{i<j} ω_i)): link j is switched on only after the driver s has passed the cumulative weight of the earlier links.

The instance used in the theorem is f(x, y) = e·F((x − x₀)/ς, (y − y₀)/ς) with e/ς = 32ε and e/ς² = ℓ/2²⁶, N the largest perfect square below ℓ/(2⁴⁶μ), and M = ⌊ℓΔ/(2⁴⁰ε²)⌋.

**Why the block is new.** Pan and Li obtain PŁ for their dual block from a perspective transform B(η, α; y) = η²G(α/η²; y/η) in the driver η. Three features of that block prevent a hiding argument against algorithms that do not respect the coordinate structure. First, its gate q(t) = 3t² − 2t³ vanishes only for t ≤ 0, so there is no positive threshold below which an undiscovered coordinate is inert. Second, the block contains −½‖y⁻‖² (the negative part of y), whose gradient reveals every hidden direction along which the query has a negative component. Third, all length scales of the block shrink with the driver η. Their bound is accordingly proved for deterministic algorithms through a resisting oracle, and they list the randomized extension, which "requires a robust saddle zero-chain", as open (Section 6). Here every gate has an absolute threshold r_j ≥ N^{−1/2}, independent of the driver, and the negative-side guard is the same function on every ambient coordinate, so it carries no information about the embedding. PŁ with modulus of order λ uniformly in the driver is recovered by the staggering: at the first gate J that is not fully open, the coordinate w_J feels a force at least α_J/(6r_J), and the total reward downstream of J is at most α_J²/(λr_J²). Without staggering the PŁ ratio degrades with the number of links (we observed this numerically before proving the lemma).

## Proof outline

1. **Block PŁ** ([NcPlBlockPL](../Proofs/NcPlBlockPL.lean), [NcPlSchedule](../Proofs/NcPlSchedule.lean)). For amplitudes satisfying two conditions (H1: an active link is at least 24λr_j² strong; H2: the downstream amplitude after an active link J is at most α_J²/(λr_J²)), the block satisfies gap ≤ (147/λ)‖∇‖². The staggered schedule satisfies H1 and H2 for every driver value.
2. **Smoothness** ([NcPlBlockSmooth](../Proofs/NcPlBlockSmooth.lean), [NcPlChain](../Proofs/NcPlChain.lean), [NcPlLipschitz](../Proofs/NcPlLipschitz.lean)). Because r_j² = ω_{j+1}, all second derivatives are bounded by universal constants, and both partial gradients of F are jointly 2²⁶-Lipschitz.
3. **Global PŁ and attainment** ([NcPlPL](../Proofs/NcPlPL.lean)). Inside the ball ‖y‖ ≤ B_y the function is separable into blocks plus the free coordinates. Outside, ⟨∇_y F, y⟩ ≤ −λ‖y‖² + 40M forces a large gradient.
4. **Moreau non-stationarity** ([NcPlMoreau](../Proofs/NcPlMoreau.lean)). Let x̄ be the proximal point of x̂. If ‖x̄‖ ≤ B_x − 1 and i is the first chain coordinate of x̄ below 1, then increasing that coordinate by t decreases Φ by at least t/16 − t²/32: at the maximizer of the perturbed problem all gates of block i are open (a consequence of the block PŁ argument), the next block's contribution is monotone in its front, and the quadratic term costs at most t/16. If ‖x̄‖ > B_x − 1, moving radially inward gives the same decrease. Proximal optimality then gives ‖∇Φ_{1/(2ℓ)}(x̂)‖ ≥ 1/16 in unscaled units whenever the last chain coordinate of x̂ is small. No differentiability of Φ is used.
5. **Oracle** ([NcPlOracle](../Proofs/NcPlOracle.lean), [NcPlOracleStats](../Proofs/NcPlOracleStats.lean)). The stage s of a query is the first position after which all hidden coordinates are below a tiny threshold θ. The reply is known_s + coin·(∇F − known_s), where known_s is the gradient of the chain truncated at s, and the coin is Bernoulli(q)/q when position s is a bulk dual link (2j ≤ n) and 1 otherwise. On bulk links ‖∇F − known_s‖ ≤ N^{−1/2}, so the variance is (1/q − 1)/N and q ≍ ε²/(κσ²) is admissible.
6. **Hiding** ([NcPlHiding](../Proofs/NcPlHiding.lean), [NcPlFailure](../Proofs/NcPlFailure.lean)). For a uniformly random embedding, with probability at least 7/8 no query has a large coordinate at an undiscovered position. On that event the transcript reveals one new bulk link only when the coin succeeds, so T·q ≥ MN/16 is needed for T calls to reach the last primal coordinate. Markov's inequality on the number of successes finishes the proof.

Multiplying M ≍ ℓΔ/ε² blocks, N ≍ κ bulk links per block and 1/q ≍ 1 + κσ²/ε² calls per link gives the budget.

## Relation to prior work

- **Pan and Li, [arXiv:2608.26799](https://arxiv.org/abs/2608.26799), Theorem 3.2.** Ω(κℓΔ/ε²) for deterministic first-order algorithms with an exact oracle. The present theorem covers all randomized algorithms and adds the noise term. Their oracle also returns function values; ours returns gradients only, so at σ = 0 the present theorem is a randomized lower bound in the gradient-only model and does not by itself settle their open direction for value-and-gradient oracles.
- **Zero-respecting algorithms.** For algorithms whose queries stay in the span of earlier replies, we expect that the κ² noise term can be obtained from Pan and Li's chain combined with the probabilistic zero-chain masking of Arjevani et al. ([arXiv:1912.02365](https://arxiv.org/abs/1912.02365)); we have not written that argument out and do not claim it. The contribution here is the robust block, which makes the bound hold against arbitrary randomized algorithms.
- **Class comparison.** The class here bounds the potential-type Δ, which controls the initial dual gap as well as the primal gap. It is therefore smaller than Pan and Li's primal-gap class, and a lower bound on the smaller class transfers to theirs. Some control of the initial dual variable is needed for any finite upper bound in the stochastic setting (see [arXiv:2610.00229](https://arxiv.org/abs/2610.00229)).
- **Nonconvex–strongly-concave lower bounds.** Li et al. ([arXiv:2104.08708](https://arxiv.org/abs/2104.08708)) and Zhang et al. ([arXiv:2103.15888](https://arxiv.org/abs/2103.15888)) give √κ for exact gradients; recent stochastic bounds ([arXiv:2609.35206](https://arxiv.org/abs/2609.35206), [arXiv:2609.30877](https://arxiv.org/abs/2609.30877), [arXiv:2610.00229](https://arxiv.org/abs/2610.00229)) give κℓΔσ²/ε⁴. These transfer to the PŁ class but are a factor κ below the upper bound in the noise term.
- **Ha, [arXiv:2610.07814](https://arxiv.org/abs/2610.07814).** Lower bounds specific to two-timescale SGDA. They do not bound other algorithms.
- **Upper bound.** Yang et al. 2022, Theorem 4.1. See the [companion note](StochasticNonconvexPLUpperBound.md).

## Limitations

- The constants 2⁻⁹⁴ and 2⁻⁵⁹ are far from sharp.
- The bound needs a large ambient dimension, κ ≥ 2⁴⁷ and ℓΔ/ε² ≥ 2⁴⁷.
- Δ is the potential-type initialization of the Smoothed-AGDA analysis, not the primal gap alone.
- The oracle has no function values, and the noise model is bounded variance of the joint gradient. Mean-squared-smooth oracles, where variance reduction changes the rate, are not covered.
- The dual variable of the hard instance is unconstrained and the instance is not concave in y; the result says nothing new about the strongly concave subclass.
