# AffineResidualFiniteMaximum: novelty assessment

The [theorem](../../LongTails/Theorems/AffineResidualFiniteMaximum.lean) proves the following guarantee in the [SmoothFiniteMaximum setup](../../LongTails/Setups/SmoothFiniteMaximum.lean). Take `m ≥ 2` components that are convex on the ball `B(x₀,R)`, with gradients bounded by `G` and `L`-Lipschitz there. Each call to the exact single-component value-and-gradient oracle counts once. The randomized [algorithm](../../LongTails/Algorithms/AffineResidualFiniteMaximum.lean) then returns a feasible point with `Pr{max_i f_i(out) − max_i f_i(x⋆) ≤ ε} ≥ 1−δ`, where `x⋆` is the constrained minimizer, under a deterministic cap on the number of calls.

**Proved budget.** The budget is `n·⌈10²² h⁸ S⌉`. Here `n = 1+⌈log₂⌈1/δ⌉⌉`, `h = 1+⌈log₂⌈2+m+GR/ε+LR²/ε⌉⌉`, and `S` is the bracket below. Up to universal constants, this gives

`O( log(2/δ) · log⁸(2+m+GR/ε+LR²/ε) · [ m + m(LR²/ε)^{2/5} + m^{3/4}(LR²/ε)^{1/2} + (LR²/ε)^{2/3} ] )`.

Below, `a = GR/ε` and `b = LR²/ε`. The gradient bound `G` appears only inside the logarithm. The formula holds for all valid parameters, including `L = 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| AGD on the linearization of max-type functions (Nesterov, *Lectures on Convex Optimization* 2018, §2.3). Listed as the smooth baseline in [Carmon–Jambulapati–Jin–Sidford SODA 2024](https://arxiv.org/abs/2311.10886), Table 1. | `m(1+√b)`, deterministic → the bound above | For `b ≥ 1` and `m ≥ b^{1/6}`, it is better by the factor `min{b^{1/10}, m^{1/4}, m b^{−1/6}}` up to logarithms. This holds for every `G`. | None. The setup is the same ball-constrained convex smooth class. | None. A deterministic guarantee converts to probability `1−δ` for free. | Worse when `m ≪ b^{1/6}`, because of the term `b^{2/3}`. The new method is randomized and has `log⁸ · log(1/δ)` factors. AGD needs an exact QP over the simplex in every step, but this is internal computation. |
| SODA 2024 [Thm 8.1](https://arxiv.org/abs/2311.10886) (arXiv v1, 17 Nov 2023; evaluation count from Table 1). | `m b^{1/3} + a²`, valid only when `ε ≤ min{LR², G²/L}` → the bound above | `a²` → `m b^{2/5} + m^{3/4}√b + b^{2/3}`. It is better iff `a² ≫ m b^{2/5} + m^{3/4}√b + b^{2/3}`. | The condition `ε ≤ min{LR², G²/L}` is dropped. The instances it excludes are already covered by AGD, so this is not substantive. | Expected error → probability `1−δ`. SODA's guarantee also converts via Markov, a cost cutoff, and `O(log 1/δ)` repetitions, so there is no real gain. | Worse when `a²` is below the new bracket. For example, it is worse by the factor `b^{1/15}` when `m b^{2/5}` dominates both bounds. SODA also covers the simplex setup and bounds runtime. The new result bounds only oracle calls. |
| Carmon et al. COLT 2021 ([arXiv Thm 2](https://arxiv.org/abs/2105.01778), smooth case) | `m a^{2/3} + √m(a+√b)` up to logarithms, with probability 99/100 → the bound above | Better when `a` is large, for example in the scaling `G=L=R=1` below. | Overlapping, not nested: COLT is unconstrained, with global assumptions and `‖x₀−x⋆‖ ≤ R`; this result needs assumptions only on the ball. | None | Worse for small `a` relative to `b`. Example: `G=R=1`, `L=ε^{−2}` gives `mε^{−6/5}+m^{3/4}ε^{−3/2}+ε^{−2}` here, against `mε^{−2/3}+√m ε^{−3/2}` for COLT. |
| Repository [AffineSoftmaxFiniteMaximum](AffineSoftmaxFiniteMaximum.md) (6 Nov 2026, unpublished; same setup) | `m + m b^{1/3} + m^{3/4}√b + m^{6/7}(ab)^{2/7} + a` with `log⁷` → the bound above | The terms `m^{6/7}(ab)^{2/7} + a` are replaced by `m b^{2/5} + b^{2/3}`. It is better when `G` is large relative to `L`. | None | None | It is worse in the large-`m` regime, where `m b^{1/3}` dominates. It carries one extra logarithmic power. |

**Normalized comparison.** Take `G=L=R=1` and `m=ε^{−γ}`, and ignore polylogarithms. The new bound has order `ε^{−max{γ+2/5, 3γ/4+1/2, 2/3}}`. The best published bound has order `ε^{−min{γ+1/2, 2}}` for `γ ≤ 5/3`; above that, SODA's `γ+1/3` takes over.

- The new bound is strictly better than the best published bound for `1/6 < γ < 8/5`.
- Including the repository result, it is strictly better for `1/6 < γ < 6/5`.
- Against the published bounds the gain is at most `ε^{−1/10}`, attained for `2/5 ≤ γ ≤ 3/2`.
- At `γ=1/2`, the gap to the COLT lower bound `Ω(m b^{1/3} + √(mb))` narrows from `1/6` to `1/15` in the exponent. That lower bound is arXiv Thm 3, which needs high dimension.

**Reduction check and proof ancestry.** I found no standard reduction that yields this rate:
- Batching the SODA moving-Gibbs estimator scales variance and cost together.
- AGD on the linearization pays `m` calls per step.
- Generic stochastic mirror-prox bounds do not give the needed residual-only dual variance `mD_r²/τ`.

What looks new is the local solver. It caches the affine part and samples only the nonlinear residual `d_i = f_i − ℓ_i ∈ [0, Lr²/2]` for both players. A future-comparator FTRL bound on that solver allows balls with `Lr² ≫ τ`. SODA §1.1 explicitly left variance reduction on larger balls open.

Proof ancestry, not counted as baselines:
- ball acceleration (Carmon et al. 2020, SODA 2024 §4);
- the multilevel and local-to-global outer loop ([Carmon–Hausler NeurIPS 2022](https://arxiv.org/abs/2203.13225));
- generic FTRL and entropy tools.

These supply the outer loop only. The local guarantee and the radius balancing are what produce the exponents.

I spot-checked `trial_budget_le` and `successful_execution` and grepped for `sorry`/`admit`/`axiom` (none found). I did not run the build or the comparator.

**Search coverage (12 Nov 2026 UTC).** Sources I read directly:
- the theorem statements and tables of the COLT and SODA arXiv texts;
- the Semantic Scholar forward citations of both papers through Nov 2026.

The following citing papers or leads do not compete, for the stated reasons:

| Paper | Reason it does not compete |
|---|---|
| 2509.04426, 2601.02347, 2607.04062 | Matrix-vector oracles for bilinear problems |
| 2509.24894 | LogSumExp surrogate SGD |
| 2609.32872 | Near-active top-`k` assumption, `ε^{−2}` |
| 2403.03562 | Two-level finite sums |
| 2601.14680 | Full oracle plus quadratic growth |
| [2611.00317](https://arxiv.org/abs/2611.00317) | Finite sums inside each constraint. One call evaluates all `m` constraints, so it gives no component-oracle bound. |

I did not check venue status of the 2026 preprints, and the OpenReview item mentioned in the note is unverified. The note's formulas and regimes match the Lean budget and the sources. The one discrepancy is that the note cites COLT "Theorem 6", which is not the arXiv numbering (Thm 2).

## Conclusion

**Yes. For a wide middle range of component counts, the proved query complexity is polynomially better than every applicable published bound I found.**

The strongest baselines are AGD on the linearization and the SODA 2024 ball method.

| | Oracle calls (polylogarithms suppressed) |
|---|---|
| AGD on linearization | `m√b` |
| SODA 2024 (needs `ε ≤ G²/L`) | `m b^{1/3} + a²` |
| This result | `m + m b^{2/5} + m^{3/4}√b + b^{2/3}` |

The result beats AGD whenever `m ≥ b^{1/6}`, by up to a factor of `b^{1/10}`, regardless of `G`. It beats SODA whenever `a² ≫ m b^{2/5} + m^{3/4}√b + b^{2/3}`. With `G=L=R=1` and `m=ε^{−γ}`, it is strictly best among published bounds for `1/6 < γ < 8/5`; for example, at `m=ε^{−1}` the bound improves from `ε^{−3/2}` to `ε^{−7/5}`.

It loses in three places:
- to AGD for very small `m`;
- to SODA for very large `m`;
- to COLT 2021 when `L ≫ G²/ε`.

The gain is at most `ε^{−1/10}`, and the bound carries `log⁸` and a constant of `10²²`. It is therefore asymptotic, not practical.

The comparison establishes the gain. Priority rests on forward-citation tracing that found no later or concurrent competitor, but that search cannot rule out unindexed work. The gain comes from a new residual-sampling local saddle solver, not from tuning.

The claimable contribution is a new upper bound for component-oracle complexity of smooth finite maxima. It narrows the gap to the known lower bound in that middle regime, with no optimality claim and no practical speedup.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
