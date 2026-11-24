# Stochastic nonconvex optimization under generalized smoothness of order ρ < 2: lower bound

The [main theorem](StochasticEllSmoothLowerBound.lean) is a `NonConvergence` result for the high-dimensional
restriction [`HighDimensionalStochasticEllSmoothNonconvex`](../Setups/HighDimensionalStochasticEllSmoothNonconvex.lean)
of the class used by the companion [upper bound](StochasticEllSmoothUpperBound.md).

## Setup

The class is that of [`StochasticEllSmoothNonconvex`](../Setups/StochasticEllSmoothNonconvex.lean), with `E = ℝ^d` and
sample space `ℝ`, through `toGeneral`. Admissibility and success are those predicates applied to `toGeneral q`, so
every hard instance is literally an admissible instance of the upper-bound class.

- **Objective.** `f` has a differentiable gradient, satisfies `‖∇²f‖ ≤ ℓ(‖∇f‖)` with `ℓ` regular of order `ρ < 2`,
  and `f(x₀) − f(x) ≤ Δ` for all `x`.
- **Oracle.** IID samples and gradient-only replies. The oracle is unbiased, jointly measurable, and has central
  `p`-th moment at most `σ^p`, with `p ∈ (1,2]`.
- **Success.** `E‖∇f(x̂)‖ ≤ ε`.

`valid` adds three conditions:

- `ℓ(0) > 0`;
- `2²⁸ε² ≤ (2−ρ)Δℓ(ε)`, so the instance is not trivial;
- a dimension condition `d ≥ 2⁵⁶(Y/2²⁷+1)⁶(ℓ(ε)/ℓ(0))⁴`, where
  `Y = (2−ρ)T̄·max{1, (σ/(2¹³ε))^{p/(p−1)}}` and `T̄ = Δℓ(ε)/ε²`. Since `Y/2²⁷` bounds both the chain length and the
  budget, one condition covers PR #244's dimension requirement and the counting over queries.

These are the restrictions of PR #244's deterministic lower bound, with the dimension enlarged to account for the
stochastic budget. The regime is nonempty: take `ℓ(u) = L₀ + L_ρu^ρ`, `ε` small, and `d` large. The budget is
nonzero, so the statement is non-vacuous, only when `(2−ρ)T̄·max{1,(σ/(2¹³ε))^{p/(p−1)}} ≥ 2³²`. At the smallest
valid value `(2−ρ)T̄ = 2²⁸` with small noise the budget is `0`.

## Result

For every valid parameter, every randomized algorithm, and every budget `b ≤ budget` (including `b = 0`), there is an
admissible instance on which the algorithm fails, that is, `E‖∇f(x̂)‖ > ε`. The budget is

```
⌊(2 − ρ) · T̄ · max{1, (σ/(2¹³ε))^(p/(p−1))} / 2³²⌋,   T̄ = Δℓ(ε)/ε².
```

The hard instance depends on the algorithm and the budget, through a counting argument over embeddings, but not on
the realized seed.

## Hard instance

1. **Objective.** The objective is exactly PR #244's hard function, with its shape and scale
   (`EllSmoothLowerBound.shape` and `.scale`, `a/λ = 8ε`):
   - a two-sided Carmon chain of length `n + 1 = ⌊(2−ρ)T̄/2²⁷⌋ + 1`;
   - a terminated power-law tail profile;
   - a norm cut-off and quadratic wall;
   - a random coordinate embedding.

   Membership in the ℓ-class, the gap condition, and `‖∇f‖ ≥ 4ε` at unfinished points are reused from PR #244
   (`instance_admissible`, `hgrad_far`, `hgrad_near_unfinished`).
2. **Masked oracle** ([`StochasticEllSmoothMask`](../Proofs/StochasticEllSmoothMask.lean)).
   - **Reply.** `g(x, ω) = K_s(x) + coin_q(ω)·(∇f(x) − K_s(x))`.
     - `K_s` is the gradient of the chain truncated at the current stage `s`, the last coordinate exceeding `1/4`
       (`EllSmoothSimulation.pgrad`).
     - `coin_q = 1/q` with probability `q` and `0` otherwise (PR #185's `coin`), with
       `q = 1/max{1, (σ/(2¹³ε))^{p/(p−1)}}`.
   - **Uniform bound on the masked part** (`secret_bound`). `‖∇f − K_s‖ ≤ 512·a/λ = 4096ε` uniformly in `x`.
     - The truncated and full chain fields differ in at most two coordinates, each bounded by PR #244's link
       bounds.
     - The cut-off derivative term is at most `O((n+1)/rad) ≤ 1`.
     - Far from the chain (`‖w‖ > 4·rad`), the masked part vanishes.

     Only the frontier link term is masked, so the wall and cut-off parts carry no noise.
   - **Moments.** The oracle is unbiased. Its `p`-th moment is exactly `‖∇f − K_s‖^p·(q(1/q−1)^p + (1−q))`, which is
     `≤ σ^p`. When `q = 1` the noise vanishes; otherwise the moment is `≤ 2q^{1−p}(4096ε)^p = 2^{1−p}σ^p`.
3. **Hiding and counting** ([`StochasticEllSmoothLower`](../Proofs/StochasticEllSmoothLower.lean)).
   - A coupling with a simulated run that uses only the first `level` embedded coordinates (`coupling`) shows that
     new chain coordinates can be revealed only by coin successes. Here `level` counts coin successes, PR #185's
     `level`.
   - PR #185's `bounded_prefix_bad_count` shows that at most `1/8` of embeddings are hit by the queries.
   - With `N ≤ budget`, the expected number of coin successes is at most `(2−ρ)T̄/2³²`, so at least `15/16` of seeds
     have fewer than `n/2` successes.
   - On such seeds, for good embeddings, the output is unfinished and `‖∇f(x̂)‖ ≥ 4ε`.
   - Averaging over embeddings gives an embedding with `E‖∇f(x̂)‖ ≥ 4ε·(7/8)(15/16) > ε`.

## Contribution and comparison

| Result | Class | Algorithms | Bound |
|---|---|---|---|
| Arjevani et al., Math. Program. 2023 (Thm 3); Zhang et al. NeurIPS 2020; Fradin et al. [arXiv:2512.18713](https://arxiv.org/abs/2512.18713) | `L`-smooth (`ℓ ≡ L`), variance / `p`-BCM | randomized | `Ω(LΔ/ε² · (1+(σ/ε)^{p/(p−1)}))` |
| PR #244 (repository; in [arXiv:2611.13872](https://arxiv.org/abs/2611.13872)) | ℓ regular of order `ρ < 2`, exact oracle | randomized | `Ω((2−ρ)Δℓ(ε)/ε²)` |
| Liang–Luo, [arXiv:2610.21692](https://arxiv.org/abs/2610.21692) v2 (preprint) | `(L₀,L₁)` (`ρ = 1`), `p`-BCM | arbitrary randomized first-order | `Ω((1+(σ/ε)^{p/(p−1)})(L₀Δ/ε² + L₁Δ/ε))` |
| **This theorem** | ℓ regular of order `ρ < 2`, `p`-BCM, gradient-only | randomized | `Ω((2−ρ)·(Δℓ(ε)/ε²)·max{1, (σ/(2¹³ε))^{p/(p−1)}})` |

What is new is the stochastic lower bound for generalized smoothness of order `ρ ∈ (1,2)`, which captures both the
`ℓ(ε)` and the noise dependence. For `ρ ≤ 1` and `ℓ = L₀ + L₁u` it recovers the form of Liang–Luo's bound up to
constants.

The proof combines two existing repository pipelines, so we call it a routine combination:

- PR #244's chain and its ℓ-class verification;
- PR #185's Bernoulli masking, coupling, and coin counting.

The one genuinely new technical piece is the uniform bound on the masked part for the ℓ-smooth chain, with its
explicit constant `512`. This is what makes the noise level, and hence the `p`-dependent constant `2¹³`, explicit.

## Relation to the upper bound

The two theorems use the same class, oracle model, and accuracy criterion. The lower-bound setup restricts the
upper-bound setup to `ℝ^d` with large `d` and adds `ℓ(0) > 0` and `T̄ ≥ 2²⁸/(2−ρ)`.

In this regime, the ratio of the [upper budget](StochasticEllSmoothUpperBound.lean) to the lower budget is
`O(2^{c·p/(p−1)} · log₂(2+T̄)/(2−ρ)²)`. The pair therefore determines the complexity
`Θ̃((1 + (σ/ε)^{p/(p−1)})·Δℓ(ε)/ε²)` up to:

- one logarithmic factor;
- a polynomial factor in `1/(2−ρ)`;
- a constant depending only on `p`.

This holds for every regular `ℓ` with `ρ < 2`.

## Limitations

- The `log₂(2+T̄)` factor of the upper bound is not matched. Whether it is necessary for `ρ ∈ (1,2)` under
  heavy-tailed noise is open.
- The `(2−ρ)` factor comes from PR #244's chain and degenerates as `ρ → 2`. `ρ = 2` is excluded.
- `ℓ(0) > 0` and polynomially large dimension are required, as in PR #244. Nothing is claimed in low dimension.
- The constants (`2³²`, `2¹³`) are conservative and were not optimized.

## Scope (task requirements)

This is the `NonConvergence` half of an almost tight upper/lower pair, in Template/TemplateLowerBound terms, for
stochastic generalized-smooth nonconvex optimization.

- **Where it is new.** The new range is the sub-quadratic class `ρ ∈ (1,2)` of Li et al. and Tyurin. At `ρ = 1`,
  Liang–Luo already give a randomized lower bound of the same form.
- **Overlap.** It does not overlap with existing repository results (PR #244 is deterministic) or with open PRs.

## Lean

- **Setups:** [`HighDimensionalStochasticEllSmoothNonconvex`](../Setups/HighDimensionalStochasticEllSmoothNonconvex.lean),
  which restricts [`StochasticEllSmoothNonconvex`](../Setups/StochasticEllSmoothNonconvex.lean).
- **Proofs:**
  - [`StochasticEllSmoothMask`](../Proofs/StochasticEllSmoothMask.lean): masked part, reply, coin moments, coupling.
  - [`StochasticEllSmoothLower`](../Proofs/StochasticEllSmoothLower.lean): measurability, counting, admissibility,
    failure.
