# Novelty assessment: BlockHeterogeneousLowerBound

**Guarantee.** The [theorem](../../LongTails/Theorems/BlockHeterogeneousLowerBound.lean) is a `NonConvergence` result on the [high-dimensional setup](../../LongTails/Setups/HighDimensionalBlockHeterogeneousNonconvex.lean), which restricts the [general block setup](../../LongTails/Setups/BlockHeterogeneousNonconvex.lean). It shows that every randomized algorithm fails on some admissible instance at every budget `b ≤ ⌊(‖L‖₁Δ/ε² + S³Δ/ε⁴)/2⁵⁷⌋`. Here an admissible instance is a block-smooth function with an unbiased IID oracle whose per-block variance is bounded, and failure means `E Σⱼ‖Pⱼ∇f(x̂)‖ > ε`. The theorem constructs no algorithm. The matching upper bound is the separate [BlockSgd](../../LongTails/Algorithms/BlockSgd.lean) theorem.

**Simplified bound.** At least

$$N=\Omega\Big(\tfrac{(\sum_j L_j)\Delta}{\varepsilon^2}+\tfrac{(\sum_j L_j^{1/3}\sigma_j^{2/3})^3\Delta}{\varepsilon^4}\Big)$$

calls are required, with the explicit constant 2⁻⁵⁷ and no logarithms. The parameters are:
- `B` blocks;
- `Lⱼ`, the two-sided block-smoothness constants;
- `σⱼ²`, the per-block variances;
- `Δ ≥ f(x₀) − inf f`;
- `ε`, the target for the expected sum of block-gradient norms.

The bound holds only under two restrictions:
- `2⁵⁷ε² ≤ LⱼΔ` for **every** block `j`;
- every block has dimension at least `2⁴⁰(1 + B(ΣLᵢ)Δ/ε² + (Σᵢ(Lᵢσᵢ²)^{1/3})³Δ/ε⁴)⁴`.

The sample space is fixed to ℝ. The quantifiers match `AGENTS.md`: every valid parameter choice, every algorithm, and every `b ≤ budget`. The instance depends on the algorithm (through a word tuple chosen by counting), not on its seed. The companion upper bound `⌈8ΣLⱼΔ/ε² + 20S³Δ/ε⁴⌉+1` closes the gap to a universal constant inside this regime.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Arjevani et al., Math. Program. 2023](https://arxiv.org/abs/1912.02365), randomized ε⁻⁴ lower bound (ℓ₂, single `L,σ`). Restriction: `B=1`; applied here by embedding it in one block (the other blocks are zero, the criterion becomes `‖∇f‖₂`) | `Ω(maxⱼ[LⱼΔ/ε² + Lⱼσⱼ²Δ/ε⁴])` → `Ω(ΣLⱼΔ/ε² + (ΣLⱼ^{1/3}σⱼ^{2/3})³Δ/ε⁴)` | Up to a factor `B` in the deterministic term and `B³` in the noise term. Example: equal blocks give `Lσ²Δ/ε⁴ → B³Lσ²Δ/ε⁴`. None when one block dominates both sums | `B=1` → `B` heterogeneous blocks with the sum-of-block-norms criterion | None | Every block must satisfy `2⁵⁷ε² ≤ LⱼΔ`, and every block needs very high dimension. Constant 2⁻⁵⁷ |
| [Jiang–Maladkar–Mokhtari, COLT 2025](https://arxiv.org/abs/2406.04592), Thm 3.3. Restriction: deterministic algorithms, σ=0, coordinate model (embeds into blocks) | `Ω(‖L‖₁Δ/ε²)` (deterministic algorithms only) → the bound above (randomized algorithms) | Adds the noise term. This is a polynomial gain when `(ΣLⱼ^{1/3}σⱼ^{2/3})³ > ε²ΣLⱼ` | Deterministic algorithms → all randomized algorithms; noiseless → per-block variance | None | Their bound has no regime or dimension condition and holds for blocks of size 1. This one needs huge blocks |
| Same paper, Thm 3.2. Restriction: AdaGrad only, coordinate model | `Ω((‖L‖₁Δ/ε² + (ΣLᵢ^{1/3}σᵢ^{2/3})³Δ/ε⁴)·log)` for AdaGrad → same polynomial order for every randomized algorithm | None in order; for AdaGrad specifically, their bound is larger by the log factor | AdaGrad → whole algorithm class (on high-dimensional blocks) | None | The per-coordinate ℓ₁ model (blocks of size 1) is not covered |

**Reduction check and mechanism.** The single-block embedding gives only the maximum over blocks. In the homogeneous case (equal `L,σ` and block sizes), a randomly rotated isotropic Arjevani instance with total variance `Bσ²` plausibly gives `B³Lσ²Δ/ε⁴` already. That rotation spreads the gradient so that `Σⱼ‖Pⱼ∇f‖ ≈ √B‖∇f‖`. I did not check the needed uniform concentration, and I see no such reduction for heterogeneous `(Lⱼ,σⱼ)`.

The ingredients are known:
- the masked probabilistic chain of Arjevani et al. (via the repository's AbcNoise instance);
- the `σⱼ^{2/3}Lⱼ^{1/3}` allocation, taken from the AdaGrad-specific instance of Jiang et al. Thm 3.2.

The added step is the composition across blocks: the other blocks are simulated inside a single-block deterministic algorithm, with a shared coin and averaging over word tuples. This simulation is standard, but it is what makes the bound hold for every randomized algorithm.

**Search coverage (2026-11-19).** I searched arXiv and proceedings for all-algorithm lower bounds under coordinate, block or layer smoothness and ℓ₁/ℓ∞ geometry. I read the theorem statements of Jiang et al. (v3, June 2025), [Tao–Yu–Zhang 2605.06615](https://arxiv.org/abs/2605.06615) (May 2026; lower bounds for SignSGD, SGD and Muon only) and [Jin 2608.09004](https://arxiv.org/abs/2608.09004) (Aug 2026; Euclidean, bounded noise). None gives this bound for all algorithms. Arjevani et al.'s theorem numbering and appendices, and the appendices of Jiang et al., were not read verbatim. The companion note's citations are consistent with these sources. The result entered the repository in commit 24ba0905 (2026-11-19).

## Conclusion

**Yes: within its regime, this is a new lower bound for every randomized algorithm, larger than the bound from known reductions by up to a factor of B³.**

The strongest prior bound for all algorithms on this class comes from embedding Arjevani et al. in one block. Jiang et al. have the same `S³` quantity, but only for AdaGrad, and their all-algorithm bound covers deterministic methods without noise.

| | necessary calls |
|---|---|
| prior (embedding) | `maxⱼ(LⱼΔ/ε² + Lⱼσⱼ²Δ/ε⁴)` |
| this result | `(ΣLⱼ)Δ/ε² + (ΣLⱼ^{1/3}σⱼ^{2/3})³Δ/ε⁴` |

With the companion block-preconditioned SGD bound, this pins down the class complexity up to a universal constant. It also shows that the `‖L‖₁‖σ‖₁²` noise factor in AdaGrad's upper bound is not the class rate.

The limits are real:
- Every block must be nontrivial (`ε² ≤ 2⁻⁵⁷LⱼΔ`), and every block must be very high-dimensional.
- The per-coordinate ℓ₁ model studied by Jiang et al. remains open.
- The homogeneous case might follow from a rotated Arjevani instance; I did not check this.
- The proof composes known chains and allocations, so its technical novelty is moderate.

The comparison establishes the gain over the checked baselines. My search found no earlier all-algorithm bound of this form, but that does not prove priority. The claimable contribution is a tight characterization of block-heterogeneous stochastic nonconvex complexity for all randomized algorithms, restricted to the case where every block is nontrivial and high-dimensional.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
