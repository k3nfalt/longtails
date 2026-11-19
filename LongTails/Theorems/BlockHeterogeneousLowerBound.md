# Block-heterogeneous stochastic nonconvex optimization: matching randomized lower bound

Lean: [theorem](BlockHeterogeneousLowerBound.lean), [setup](../Setups/HighDimensionalBlockHeterogeneousNonconvex.lean) (which reuses the [general block setup](../Setups/BlockHeterogeneousNonconvex.lean)), and proofs [BlockEmbedding](../Proofs/BlockEmbedding.lean), [BlockLowerInstance](../Proofs/BlockLowerInstance.lean), [BlockLowerBound](../Proofs/BlockLowerBound.lean) and [BlockLowerParameters](../Proofs/BlockLowerParameters.lean). The matching upper bound is in [BlockHeterogeneousSgdUpperBound](BlockHeterogeneousSgdUpperBound.md).

## Setup and claim

The problem class, oracle and criterion are those of the block-heterogeneous setup:
- two-sided block smoothness with constants `L_j`;
- an unbiased IID stochastic gradient with per-block variance at most `σ_j²`;
- `f(x_0) − inf f ≤ Δ`;
- success means `E Σ_j ‖P_j ∇f(x̂)‖ ≤ ε`.

The high-dimensional setup keeps the same instances and success criterion. It fixes the sample space to `ℝ` and restricts the parameters to the regime

- `B ≥ 1`, `L_j > 0`, `σ_j ≥ 0`, `ε > 0`;
- `2^57 ε² ≤ L_j Δ` for **every** block `j`;
- every block has at least `2^40 (1 + B‖L‖₁Δ/ε² + S³Δ/ε⁴)^4` coordinates, where `S = Σ_j (L_jσ_j²)^{1/3}`.

**Theorem** (`NonConvergence`). Every randomized algorithm fails at every budget `b ≤ ⌊(‖L‖₁Δ/ε² + S³Δ/ε⁴)/2^57⌋` on some admissible instance and oracle. Here a randomized algorithm may depend on all parameters, use private randomness, and choose its output arbitrarily. The instance may depend on the algorithm and on `b`, but not on the realized seed.

Together with the upper bound `⌈8‖L‖₁Δ/ε² + 20S³Δ/ε⁴⌉ + 1`, this gives

`Θ( (Σ_j L_j) Δ/ε² + (Σ_j L_j^{1/3} σ_j^{2/3})³ Δ/ε⁴ )` oracle calls

for known parameters in this regime, tight up to a universal constant (≈ 20·2^57). The upper bound is proved on the general setup and applies verbatim here: the high-dimensional `valid` implies the general `valid`, and `admissible` and `successful` coincide at `toGeneral q`. With `B = 1` it reduces to the bound of [Arjevani et al. (Math. Program. 2023)](https://arxiv.org/abs/1912.02365).

## Hard-instance construction

The construction has five ingredients:
1. **Per-block chains.** Each block `j` hosts an independent copy of the repository's randomized masked-chain instance from [AbcNoiseLowerBound](AbcNoiseLowerBound.lean), with `A = B = 0`, in that block's coordinates. The instance consists of the hidden coordinate word, the dead-zone chain, the wall, and progress-dependent Bernoulli masking. It is placed via the isometries `restrict`/`extend` and has its own parameters `(L_j, Δ_j, ε_j, C_j ≤ σ_j²)`. The objective is `F(x) = Σ_j h_j(restrict_j x)`.
2. **Block smoothness of the sum.** Each `h_j` has an `L_j`-Lipschitz gradient. This gives the two-sided block bound for `F`, with the block gradient `P_j∇F = extend_j ∇h_j`.
3. **Shared-coin oracle.** The oracle returns `Σ_j extend_j(reply_j(restrict_j x, u))` with a single uniform coin `u` per query, shared by all blocks. It is unbiased, and its block-`j` variance is that of block `j`'s masked reply, at most `C_j ≤ σ_j²`. The class constrains only per-block moments, so this is a legitimate admissible oracle. We expect, but have not formalized, that independent per-block coins would also work.
4. **Budget allocation.**
   - *Deterministic regime*, when `S³ ≤ ‖L‖₁ε²`: `Δ_j = ΔL_j/‖L‖₁`, `ε_j = εL_j/‖L‖₁`, `C_j = 0`. Every block then has per-block hardness `‖L‖₁Δ/ε²`.
   - *Noise regime*, otherwise. Blocks with `w_j ≥ S/(2B)` are active and get `Δ_j = (Δ/2)w_j/S`, `ε_j = εw_j/S`, `C_j = σ_j²`; their hardness is `S³Δ/(2ε⁴)`. Inactive blocks get a dummy noiseless instance of the same hardness, with `ρ = ε²‖L‖₁/S³ ≤ 1`, `Δ_j = Δ ρ L_j/(2‖L‖₁)` and `ε_j = ερL_j/‖L‖₁`. Active blocks carry at least half of `S`, so `Σ_j ε_j ≥ ε/2`. The total gap is at most `Δ`.

   The allocation of `Δ` and `ε` in proportion to `σ_j^{2/3}L_j^{1/3}` mirrors the AdaGrad-specific lower bound of [Jiang–Maladkar–Mokhtari (COLT 2025), Thm 3.2](https://arxiv.org/abs/2406.04592).
5. **Composition across blocks.** This is the new formal step.
   - The criterion is an expectation of a sum, so no joint-failure event is needed: `E Σ_j‖P_j∇F‖ = Σ_j E‖∇h_j‖`.
   - Fix block `j`, the words of the other blocks, and the coin stream. The composite algorithm is then a deterministic state machine for block `j` alone. Its state is the algorithm state plus a time counter, and the other blocks' replies are computed inside it.
   - The single-block counting lemma (`block_sum_bound`) therefore applies. For good coin streams, which have probability ≥ 7/8, at most 1/8 of block-`j` words are "bad", and on good words the block gradient is at least `3ε_j`.
   - The tuple of words is split with `Equiv.piSplitAt`, and the bound is summed over blocks and averaged over all word tuples. This gives `Σ_w E Σ_j‖P_j∇F_w‖ ≥ (147/64)|W|Σ_j ε_j > |W|ε`. So some word tuple fails; the choice depends on the algorithm, not on its seed.

## Why the regime is needed, and what stays open

- **Per-block regime `2^57 ε² ≤ L_jΔ`.** This is necessary, not an artifact. Block smoothness gives `‖∇_j f(x)‖² ≤ 2L_j(f(x) − inf f)`. A block with `L_jΔ ≪ ε²` is therefore essentially free for any method that keeps `f − inf f = O(Δ)`, whatever its noise level `σ_j`. In particular, with `B = 1` and `LΔ < ε²/2`, the zero-query output `x_0` already succeeds, while `S³Δ/ε⁴ = Lσ²Δ/ε⁴` is arbitrarily large. The upper bound holds for all parameters. Outside the regime it is not tight: freezing trivial blocks would remove their `w_j` from `S`. The mixed trivial/nontrivial case is open, and we do not claim Θ there.
- **High-dimensional blocks.** The dimension requirement is kept explicit. As in all dimension-free stochastic lower bounds, each block must host a chain of length about `L_jΔ_j/ε_j²` with hidden coordinates. The polynomial threshold above comes from the reused counting argument and is far from optimized.
- **The per-coordinate ℓ1 model stays open.** This is the model of [Jiang et al.](https://arxiv.org/abs/2406.04592) and [Liu–Pan–Zhang](https://arxiv.org/abs/2406.15244), with blocks of size 1, per-coordinate `L_i, σ_i`, and criterion `‖∇f‖₁`. The pair does not close it. The upper bound still applies with `S = Σ_i L_i^{1/3}σ_i^{2/3}`. But grouping `m` identical coordinates into one block gives hardness `m(Lσ²)^{1/3}`, not `m³`. Spreading the gradient across coordinates would need chains longer than the block. In low dimension, methods such as noisy bisection beat `S³Δ/ε⁴`. A different model, homogeneous ℓ∞ geometry with a single `L` and `Σ_i σ_i ≤ S` (the SignSGD setting of [2605.06615](https://arxiv.org/abs/2605.06615)), is also not addressed here.

## Novelty and closest prior work

- [Arjevani et al. 2023](https://arxiv.org/abs/1912.02365) gives `Ω(LΔσ²/ε⁴ + LΔ/ε²)` for one block. It is the special case `B = 1`, and the per-block engine via the repository's randomized version.
- [Jiang–Maladkar–Mokhtari (COLT 2025)](https://arxiv.org/abs/2406.04592) has two lower bounds in the coordinate model:
  - Thm 3.3: `Ω(‖L‖₁Δ/ε²)`, for **deterministic** algorithms and no noise;
  - Thm 3.2: `S³` for **AdaGrad only**.

  Their lower bounds do not cover every randomized method. [Jin (2608.09004), Table 1](https://arxiv.org/abs/2608.09004) also notes this.
- [You et al. (ICLR 2020), Thm 2 (LARS) and Thm 3 (LAMB), which also assume bounded gradients](https://arxiv.org/abs/1904.00962), [Gluon](https://arxiv.org/abs/2505.13416) and [Hao et al.](https://arxiv.org/abs/2510.14009) give layer-wise upper bounds only.
- **New:** the first lower bound for **all randomized algorithms** under block-heterogeneous smoothness and noise. It establishes that `(Σ_j L_j^{1/3}σ_j^{2/3})³` is the exact noise-heterogeneity measure for the sum-of-layer-norms criterion, so the `‖L‖₁‖σ‖₁²` factor in existing layer-wise and adaptive upper bounds is not the class complexity. The techniques (masked chains, proportional allocation) are known. The contribution is the closed characterization and the composition argument. We flag its technical novelty honestly as moderate.

## Scope compliance

- The setup is important and popular: layer-wise smoothness and noise heterogeneity, as in LARS/LAMB, AdaGrad-type and layer-wise LMO optimizers.
- Both bounds are proved in Template / TemplateLowerBound, and they are tight up to a universal constant (≈ 20·2^57) on the stated regime. Their differences are the regime and dimension conditions of `valid` and the fixed sample space `ℝ`. The instances and criterion are identical.
- Reused techniques (PR #185 hard instance) are permitted by the task.
