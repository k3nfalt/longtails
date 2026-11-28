# High-probability nonconvex stationarity under heavy-tailed noise: upper bound with additive confidence cost

Lean: [`HeavyTailedHighProbabilityStationarityUpperBound.lean`](HeavyTailedHighProbabilityStationarityUpperBound.lean) (theorem `result`).
- Setup: [`Setups/HeavyTailedHighProbabilityStationarity.lean`](../Setups/HeavyTailedHighProbabilityStationarity.lean).
- Algorithm: [`Algorithms/HeavyTailedHighProbabilityStationarity.lean`](../Algorithms/HeavyTailedHighProbabilityStationarity.lean).
- Main proof: [`Proofs/HeavyTailedHighProbabilityUpper.lean`](../Proofs/HeavyTailedHighProbabilityUpper.lean).
- Supporting modules:
  - [`Step`](../Proofs/HeavyTailedHighProbabilityStep.lean): p-th-moment clipping and pilot tails;
  - [`Constants`](../Proofs/HeavyTailedHighProbabilityConstants.lean): effective variance;
  - [`PhaseOne`](../Proofs/HeavyTailedHighProbabilityPhaseOne.lean);
  - [`PhaseTwo`](../Proofs/HeavyTailedHighProbabilityPhaseTwo.lean): ladder with a biased target;
  - [`Block`](../Proofs/HeavyTailedHighProbabilityBlock.lean): bias-stable clipped tests;
  - [`Budget`](../Proofs/HeavyTailedHighProbabilityBudget.lean).

The matching lower bound is [`HeavyTailedHighProbabilityStationarityLowerBound`](HeavyTailedHighProbabilityStationarityLowerBound.md).

## Problem

This is the standard heavy-tailed stochastic nonconvex model used by Zhang et al. (NeurIPS 2020), Cutkosky–Mehta (NeurIPS 2021), Nguyen et al. (NeurIPS 2023), Hübler–Fatkhullin–He (AISTATS 2025) and Fradin et al. (AISTATS 2026, Assumption 2.3, "p-BCM").

- **Space.** `E` is a real inner-product space. It is complete, Borel and second countable, and dimension-free; every finite-dimensional Euclidean space qualifies.
- **Objective.** `f : E → ℝ` is differentiable with `L`-Lipschitz gradient. `fstar = inf f` is finite, and `f(x0) − fstar ≤ Δ`.
- **Oracle.** One query at `x` returns `g(x, ξ_k)`:
  - the samples `ξ_k` are IID with law `μ`, and `g` is jointly measurable;
  - the oracle is unbiased: `∫ g(x, ω) dμ = ∇f(x)`;
  - the noise has a bounded central p-th moment: `∫ ‖g(x, ω) − ∇f(x)‖^p dμ ≤ σ^p`, for some `p ∈ (1, 2]`.
- **No other assumption.** There is no variance bound when `p < 2`, no sub-Weibull or symmetry assumption, and no bounded-noise assumption.
- **Parameters.** `L > 0`, `1 < p ≤ 2`, `σ ≥ 0`, `Δ ≥ 0`, `ε > 0` and `0 < δ ≤ 1/4`. There is no further restriction; in particular there is no lower bound on `δ`.
- **Criterion.** High probability for a single returned point: the output is measurable and `P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ` under the joint law of the algorithm seed and the oracle samples.

## Result

Write `s = (2^45 σ/ε)^{p/(p−1)}` and `ℓ = log(16/δ)`. The algorithm uses at most

```
⌈2^76 · ( (1 + s)·(LΔ/ε² + ℓ·log^{2+2/p}(2+ℓ)) + √(LΔ)·ℓ/ε )⌉
```

oracle calls (the public `budget`). Its output is ε-stationary with probability at least `1 − δ`.

**When the bound is δ-free.** Suppose `ℓ·log^{2+2/p}(2+ℓ) ≲ LΔ/ε²` and `ℓ ≲ (1+s)√(LΔ)/ε`. Then the budget is `O((1 + s)·LΔ/ε²)`, which is the optimal in-expectation complexity `Θ(LΔ/ε²·(1 + (σ/ε)^{p/(p−1)}))`, and it does not depend on `δ` at all. For this order:
- **Upper bound in expectation:** Hübler–Fatkhullin–He, minibatch normalized SGD.
- **Lower bound, prior work:** Zhang et al. (NeurIPS 2020, Thm 6) prove it for a bounded *raw* moment, under a gradient-size condition. Fradin et al. (Thm 3.1) prove it for zero-respecting algorithms under an additional weak-average-smoothness pair oracle.
- **Lower bound, this pair:** for the present central-moment class against all randomized algorithms, the lower bound comes from the paired lower bound at constant `δ`.

**All-δ tightness when σ/ε is large.** Let `T = LΔ/ε²` and `λ = log^{2+2/p}(2+ℓ)`. If `s′ ≥ √T`, with `s′ = (σ/(2^12ε))^{p/(p−1)}` the lower-bound noise factor, then the corner term `√(LΔ)ℓ/ε = √T·ℓ` is at most `s′ℓ`. The upper bound is then `O((1+s)(T + ℓλ))`, against the lower bound `Ω((1+s′)T + s′ℓ)`. The two agree for every `δ ≤ 1/4`, up to the factor `λ` and the universal rescaling of `σ/ε`. For any fixed `σ > 0`, this holds for all sufficiently small `ε`, because `s′ ∝ ε^{−p/(p−1)}` and `√T ∝ ε^{−1}`, with `p/(p−1) ≥ 2`.

**How confidence enters.** The confidence level enters only additively, through:
- `(1+s)·ℓ·log^{2+2/p}(2+ℓ)`: the selection phase;
- `√(LΔ)ℓ/ε`: a corner term, discussed below.

**Comparison with the lower bound.** The paired lower bound is `Ω((1+s′)LΔ/ε² + s′·log(1/δ))` with `s′ = (σ/(2^12 ε))^{p/(p−1)}`. The two bounds agree up to:
- a universal rescaling of `σ/ε` inside `(·)^{p/(p−1)}`;
- the factors listed under Limitations.

## Algorithm

All tuning lives in the `Tuning` section of the algorithm file.

**Effective variance.** Let `A = 2^45(σ/ε)^p` and `σ′ = ε·max(√A, A^{1/(2(p−1))})`, so `σ′²/ε² ≤ 1 + s`. The algorithm runs PR #229's bounded-variance tuning with `σ` replaced by `σ′` (`varianceParams`). The key inequality `2σ^p B^{2−p} ≤ σ′²` (`link_bound`) at the clipping radius `B = 2^20(σ′+ε)²/ε` gives three properties:
- a clipped-variance bound;
- a clipping-bias bound;
- a per-sample tail bound for radii at most `B`.

These match the bounded-variance analysis with `σ′`.

**Phase 1: robust normalized SGD.** This is PR #229's Phase 1 at the effective variance, for `T ≍ LΔ/ε² + ℓ` steps:

```
x_{t+1} = x_t − η ĝ_t/‖ĝ_t‖,   ĝ_t = c_t + mean_i clip_B(X_i − c_t)
```

Here `c_t` is a graded pilot. The pilot batch is doubled (`pilotSamples = 2·pilotSize`), because heavy-tailed per-sample tails at radii `2^j B` decay only like `2^{−jp}`.

**Phase 2: margin-ladder selection with bias-stable clipped tests.** The candidate pool is `2^Λ` random iterates, with `Λ = ⌈log₂(64ℓ)⌉`. Round `λ` tests each surviving candidate with `8·2^λ` blocks. Each block:
- computes a fixed-radius pilot `c` from 4 samples, at radius `2^10(σ+ε)`;
- returns the clipped mean `c + mean clip_{B₂}(X − c)` over `testSize ≍ (σ′+ε)²(Λ+1)^{2+(2−p)/p}/ε²` samples, with `B₂ = B·(Λ+1)^{1/p}`.

The blocks are aggregated by a robust center. The ladder thresholds are `ε_L/2 + (2λ+1)α` with `α = ε/(64(Λ+1))` and `ε_L = ε(1 + 2^{−18})`.

Every sample is drawn through `OracleTemplate.execute`. `plan_le_budgetH` proves that the plan length is at most `budget`.

## New mechanism

**Why the plain port fails.** A direct heavy-tailed port of the p = 2 algorithm (repo PR #229) loses a factor `Λ^{(2−p)/(p−1)}`. Its ladder needs test accuracy `α ≍ ε/Λ`, and raw median-of-means at accuracy `α` costs `(σ/α)^{p/(p−1)}`. The resulting confidence term is `ℓ·log^{1+p/(p−1)}`, which is unbounded as `p → 1`.

**The fix: test the clipped-mean target.** The tests aim at `T(x) = ∇f(x) + ∫ clip_{B₂}(g(x,ω) − ∇f(x)) dμ` rather than `∇f(x)`. Only the variance of the clipped samples then enters the accuracy cost, so each block costs `σ′²(Λ+1)^{2+(2−p)/p}/ε²`. Two facts make this work:
- **The target is close to the gradient.** `‖T − ∇f‖ ≤ 2v/B₂ ≤ ε/2^19` (`test_bias_alg`). It is paid once, not once per round.
- **Bias stability.** A block centered at a pilot `c` with `‖c − ∇f‖ ≤ D ≤ B₂/2` has mean exactly `∇f + E[ψ(V−c)]`, where `ψ = clip − id`, and `‖E[ψ(V−c) − ψ(V−∇f)]‖ ≤ 2D·P(‖V−∇f‖ > B₂/2)`. This uses that `ψ` is 2-Lipschitz (projection onto a ball is nonexpansive, `clip_nonexpansive`) and vanishes on the half-radius ball (`residual_difference`, `fiber_bound`). With `B₂ = B(Λ+1)^{1/p}`, this drift is below `α/6`, uniformly over all `Λ` rounds.

**Consequence.** The ladder drifts by `O(α)` per round with variance-type accuracy cost, so the loglog power is `3 + (2−p)/p = 2 + 2/p`. This equals PR #229's power 3 at `p = 2` and is at most 4 for every `p`.

**Other new ingredients.**
- The p-th-moment versions of the clipping lemma (`centeredClip_moments_heavy`), the sub-exponential clipped-mean tail (`clip_tail_heavy`) and the pilot tails (`pilot_tail_gen`, `pilot_scale_heavy`).
- The multiscale catastrophe accounting of PR #229, reused unchanged at the effective variance.

## Comparison with prior work (heavy-tailed, single output, high probability)

| Result | Oracle calls for `P(‖∇f(x̂)‖ ≤ ε) ≥ 1−δ`, `p ∈ (1,2]` |
|---|---|
| Cutkosky–Mehta, NeurIPS 2021 ([arXiv:2106.14343](https://arxiv.org/abs/2106.14343)), clipped normalized SGD with momentum, bounded *raw* p-th moment | `ε^{-(3p−2)/(p−1)}` × polylog(T/δ), multiplicative |
| Liu et al. ([arXiv:2302.06763](https://arxiv.org/abs/2302.06763)), central p-th moment | same rate, multiplicative log(T/δ) |
| Sadiev et al., ICML 2023 ([arXiv:2302.00999](https://arxiv.org/abs/2302.00999)); Nguyen et al., NeurIPS 2023 ([arXiv:2304.01119](https://arxiv.org/abs/2304.01119)), clipped SGD, central moment | main term × log(T/δ) or log(1/δ), multiplicative |
| Hübler–Fatkhullin–He, AISTATS 2025 ([arXiv:2410.13849](https://arxiv.org/abs/2410.13849), Thm 4) | main term × log²(1/δ)-type, multiplicative |
| Fradin et al., AISTATS 2026 ([arXiv:2512.18713](https://arxiv.org/abs/2512.18713), §6, Thm 6.1) | different class: it adds q-weak average smoothness (Assumption 2.6) and uses variance reduction; log(T/β), multiplicative |
| Armacki et al. ([arXiv:2507.09093](https://arxiv.org/abs/2507.09093)) | different class: symmetric noise, or extra conditions for its symmetrized estimators |
| Repo PR #229 (`HighProbabilityStationarityUpperBound`), p = 2 only | `(1+σ²/ε²)(LΔ/ε² + ℓ log³(2+ℓ)) + √(LΔ)ℓ/ε` |
| **This work**, all `p ∈ (1,2]` | `(1+s)(LΔ/ε² + ℓ log^{2+2/p}(2+ℓ)) + √(LΔ)ℓ/ε` |

**Open questions this addresses.**
- Hübler–Fatkhullin–He (§3.2) write that they are not aware of lower bounds specifying the optimal δ-dependence.
- Fradin et al. (§6) call optimal high-probability bounds under heavy tails "an open challenge".

With the paired lower bound, this result gives the first characterization of the high-probability complexity under heavy-tailed noise for every `p ∈ (1,2]` in which `δ` enters only additively, outside the corner regime.

**Relation to PR #229.** At `p = 2` the result reduces to the repo's PR #229 (repository work, not a publication), up to constants. The Phase-1 analysis and the ladder logic are adapted from PR #229, and the routine parts are the p-th-moment substitutions. What is new is:
- the effective-variance reduction, together with the doubled pilot needed for heavy pilot tails;
- the bias-stable clipped tests, which keep the selection cost polylogarithmic in `ℓ` with a power at most 4, uniformly in `p`.

**Related convex results.** The convex analogue of high-probability optimality under heavy tails was settled recently: [arXiv:2610.00260](https://arxiv.org/abs/2610.00260) for nonsmooth convex problems, with a directional-moment coefficient, and [arXiv:2610.28107](https://arxiv.org/abs/2610.28107) under weak-L^p noise. Their online-to-batch techniques do not cover nonconvex stationarity.

## Literature search

**Searched.**
- arXiv, 2024-11 to 2026-11: heavy-tailed nonconvex high-probability stationarity, lower bounds with `δ`-dependence, and median-of-means or clipping selection.
- AISTATS 2025 (PMLR v258: Hübler–Fatkhullin–He) and AISTATS 2026 (PMLR v300: Fradin et al.), each checked in the proceedings.
- NeurIPS 2023–2025 and ICML 2025–2026 heavy-tailed SGD papers, checked through their arXiv versions.

**Not accessible.** OpenReview submissions for ICLR 2027.

**Findings.**
- No nonconvex heavy-tailed lower bound with `δ`-dependence was found.
- No upper bound with an additive confidence term under heavy tails was found.
- The convex analogue (arXiv:2610.00260, nonsmooth convex) is settled.

## Limitations

- **Corner term.** `√(LΔ)ℓ/ε` exceeds the lower bound only when `ℓ ≳ (1+s)√(LΔ)/ε`, i.e. `δ ≤ exp(−c(1+s)√(LΔ)/ε)`. It comes from PR #229's pilot sizing, which makes catastrophe counts small. Whether it is necessary is open. For fixed `σ, L, Δ` and `ε → 0`, it never dominates.
- **Selection factor.** The confidence term carries `log^{2+2/p}(2+ℓ)`, which is 3 at `p = 2` and at most 4. Whether any polyloglog factor is necessary is open.
  - A suggested multistage fixed-point recentering of the clipped tests might give power 3 for every `p`. This is unformalized and unproved.
  - The extra `(2−p)/p` comes from enlarging the Phase-2 clipping radius by `(Λ+1)^{1/p}`.
- **Low-noise regime.** When `σ ≪ ε`, the upper confidence term `ℓ·polylog(ℓ)` exceeds the lower one `s′ℓ`. A three-valued "swap" construction, which is not formalized, suggests that the true low-noise confidence cost is at least of order `ℓ/log(ε/σ)`. Sketch:
  - take `q = σ^p/(2(4ε)^p)` and replies `∇f_±`, swapped with probability `q`, plus a compensating atom;
  - an all-swapped transcript under `+` coincides with an all-normal transcript under `−`;
  - so `n < log(1/(4δ))/log(1/q)` queries fail, when `nq ≤ 1/4`.

  That term only matters when `ℓ ≳ LΔ/ε²`, where the corner term already dominates.
- **Dimension.** The upper bound is dimension-free. The lower bound needs `d` polynomial in `LΔ(1+s)/ε²`, as the other chain lower bounds in the repository do.
- **p-dependent constants.** Both bounds are stated as `(Cσ/ε)^{p/(p−1)}`, with `C = 2^45` above and `1/2^12` below. They match only up to this universal rescaling of `σ/ε`, and the ratio `(2^57)^{p/(p−1)}` grows as `p → 1`. This is the standard form in the heavy-tailed literature (e.g. the constant `c(α)` in Zhang et al.).
- **Norm moment only.** The noise is parametrized by the norm moment `σ` only. arXiv:2610.00260 shows, for convex problems, that the sharp confidence coefficient is a directional moment. The nonconvex directional-moment refinement is open. Within the `σ`-only model the pair is tight, because the lower-bound instances are essentially one-dimensional in the noise.
- **Constants.** The constant `2^76` is loose; it was chosen for a one-line formula.

## How the result meets the task requirements

- **Important, popular setup.** Heavy-tailed stochastic nonconvex optimization with the standard p-BCM noise model and the high-probability criterion. No assumption is added.
- **Upper and lower bound in the repository framework.**
  - The upper bound is a `Convergence` theorem (`Template`) on the general setup.
  - The lower bound is a `NonConvergence` theorem (`TemplateLowerBound`) on its high-dimensional Euclidean subclass, with the same oracle and criterion.
- **Near-tight closure.** The pair is tight up to constants (with the `σ/ε` rescaling) whenever `ℓ·log^{2+2/p}(2+ℓ) ≲ LΔ/ε²` and `ℓ ≲ (1+s)√(LΔ)/ε`. When `s′ ≥ √(LΔ)/ε`, which holds for every fixed `σ > 0` as `ε → 0`, it is tight for every `δ ≤ 1/4` up to the factor `log^{2+2/p}(2+ℓ)`. Outside these regimes, the gaps are exactly the limitations above.
- **Class-level result.** There is no `allowedAlgorithm` restriction. The lower bound holds for every randomized algorithm, and the upper bound exhibits one.
