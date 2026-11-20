# High-probability stationarity under bounded variance: upper bound

Lean: [`HighProbabilityStationarityUpperBound.lean`](HighProbabilityStationarityUpperBound.lean)
(theorem `result`), setup
[`Setups/HighProbabilityStationarity.lean`](../Setups/HighProbabilityStationarity.lean),
algorithm [`Algorithms/HighProbabilityStationarity.lean`](../Algorithms/HighProbabilityStationarity.lean),
main proof [`Proofs/HighProbabilityUpperAssembly.lean`](../Proofs/HighProbabilityUpperAssembly.lean).
The matching lower bound is
[`HighProbabilityStationarityLowerBound.lean`](HighProbabilityStationarityLowerBound.lean).

## Problem

The setup is the standard stochastic nonconvex first-order setup, with no assumption
beyond those of Ghadimi–Lan and Arjevani et al.:

- `E` is a real inner-product space. It is complete, Borel and second countable, so any
  finite-dimensional Euclidean space qualifies.
- `f : E → ℝ` is differentiable and its gradient is `L`-Lipschitz.
- `fstar = inf f` is finite and `f(x0) − fstar ≤ Δ`.
- The oracle returns `g(x, ξ_k)`:
  - the samples `ξ_k` are IID with law `p`;
  - `g` is jointly measurable;
  - it is unbiased, `∫ g(x, ω) dp = ∇f(x)`;
  - its variance is bounded, `∫ ‖g(x, ω) − ∇f(x)‖² dp ≤ σ²`.
- There is no sub-Gaussian assumption, no higher moment, and no symmetry.
- Parameters: `L > 0`, `σ ≥ 0`, `Δ ≥ 0`, `ε > 0` and `0 < δ ≤ 1/4`.

**Accuracy criterion.** The criterion is a high-probability guarantee for a single
returned point. The output must be measurable, and
`P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ` under the joint law of the algorithm seed and the oracle samples.

## Result

Write `ℓ = log(16/δ)`. The algorithm uses `budget q` oracle calls:

```
⌈2^71 · [ (1 + σ²/ε²)·(LΔ/ε² + ℓ·log³(2 + ℓ)) + √(LΔ)·ℓ/ε ]⌉
```

It returns a point that is `ε`-stationary with probability at least `1 − δ`.

**When the bound is δ-free.** Suppose both of the following hold:

- `ℓ·log³(2+ℓ) ≲ LΔ/ε²`;
- `ℓ ≲ (√(LΔ)/ε)(1 + σ²/ε²)`, which holds for example when `σ² ≥ ε√(LΔ)` or `ℓ ≲ √(LΔ)/ε`.

Then the bound is `O((LΔ/ε²)(1 + σ²/ε²))`. This is the expected-accuracy complexity of
Arjevani et al., and it does not depend on `δ` at all.

**Matching lower bound.** For every `δ`, the paired lower bound
[`HighProbabilityStationarityLowerBound`](HighProbabilityStationarityLowerBound.md) is
`Ω((LΔ/ε²)(1 + σ²/ε²) + σ² log(1/δ)/ε²)`. The two bounds therefore agree up to universal
constants in the regime above. Outside it, the gaps are exactly these:

- **Confidence term, noisy case.** The upper confidence term is `(1 + σ²/ε²)·ℓ·log³(2+ℓ)`
  and the lower one is `σ²·ℓ/ε²`. When `σ ≳ ε` their ratio is `O(log³(2 + log(1/δ)))`.
- **Low-noise case.** When `σ ≲ ε` the ratio `(1 + ε²/σ²)·log³(2+ℓ)` is unbounded. At
  `σ = 0` the upper bound still carries `ℓ·log³(2+ℓ) + √(LΔ)·ℓ/ε`, while the lower bound
  has no `δ`-dependent term. This additive confidence overhead for nearly noiseless oracles
  is not shown to be necessary.
- **Corner term.** The term `√(LΔ)·ℓ/ε` matters only when `ℓ ≳ (√(LΔ)/ε)(1 + σ²/ε²)`.

## Algorithm

All tuning formulas are in the `Tuning` section of the algorithm file. Write
`S = σ + ε` and `G = √(LΔ) + ε`.

**Phase 1: robust normalized SGD.** The phase runs `T ≍ LΔ/ε² + ℓ` steps, each
`x_{t+1} = x_t − η ĝ_t/‖ĝ_t‖`, with `η = 128(Δ + ε²/L)/(Tε)`. Each step draws `m_p + m_c` samples:

1. *Graded pilot.* From `m_p` single samples, a graded median-type pilot `c_t` is computed.
   It uses the first radius `2^k B` (with `B ≍ S²/ε`, `k ≤ log(G/ε) + 4`) at which a majority
   cluster exists.
2. *Centered-clipped mean.* The estimate is `ĝ_t = c_t + (1/m_c) Σ clip_B(X_i − c_t)` over
   `m_c ≍ S²/ε²` further samples.

The pilot batch is `m_p ≍ S²/ε² + G·ℓ/(Tε)`.

**Phase 2: deterministic-margin selection.**

1. *Sampling candidates.* `J0 = 2^Λ` iterates are drawn uniformly from the trajectory using
   the algorithm seed, with `Λ = ⌈log₂(64ℓ)⌉`.
2. *Test rounds.* There are `Λ + 1` rounds. Round `λ` tests each surviving entry with an
   independent median-of-means estimate:
   - `8·2^λ` blocks of `r ≍ S²Λ²/ε²` samples;
   - accuracy `α = ε/(64(Λ+1))`;
   - pass threshold `ε/2 + (2λ+1)α`.
3. *Advancing.* The first `2^(Λ−λ−1)` passers advance.

The output is the single survivor. Every sample is drawn through `OracleTemplate.execute`.
The theorem proves that the plan length, Phase 1 plus Phase 2, is at most `budget q`
(`plan_le_budget`).

## Proof structure and new mechanism

1. **Multiscale catastrophe accounting along a nonconvex trajectory**
   (`HighProbabilityPhaseOne`, `HighProbabilityStep`).
   - *The descent inequality.* Normalized steps satisfy
     `f(x_{t+1}) ≤ f(x_t) − η(‖∇f(x_t)‖ − D_t) + Lη²/2`, with damage
     `D_t = 2 min(‖ĝ_t − ∇f(x_t)‖, ‖∇f(x_t)‖)`.
   - *Splitting the damage.* `D_t` is bounded by `2·(clipping error on the pilot-success
     event)` plus a sum over dyadic scales `t_j = 2^j B/2`, `j ≤ J ≍ log(G/S)`. Scale `j`
     contributes `8·2^j B·1{pilot error > t_j}`.
   - *The clipping error* has a uniformly bounded exponential moment (layer-cake bound on
     a vector Bernstein tail).
   - *Each catastrophe indicator* has conditional probability at most
     `(10S/t_j)^{m_p} ≤ 2^{−m_p(j+15)}`.
   - *Chernoff with scale-dependent counts.* Each sum is controlled by a Chernoff bound for
     adapted sequences over IID blocks. The count for scale `j` is
     `m_j ∝ Tε(4^{−j} + 2^{−J})/B`.
     - The first part of `m_j` absorbs the expected number of catastrophes. Its rate is
       independent of `T/ε`.
     - The second part makes the failure exponents grow linearly in `j`, so the union over
       the `log(G/ε)` scales costs only a geometric series.
   - *What this removes.* This is what removes the hidden `log(G/ε)` and `log T` factors that
     a single-threshold or per-step union bound produces.
   - *The cap.* A stopping-time-free argument keeps `‖∇f(x_t)‖ ≤ 3G` along the run
     (`trajectory_bound`).
   - *Conclusion.* With probability `1 − 2e^{−ℓ}`, at most `3T/64` iterates have
     `‖∇f‖ > ε/2`.
2. **Deterministic-margin selection** (`HighProbabilityPhaseTwo`, `HighProbabilityRoundStep`).
   - *The invariant.* In each round at most a third of the entries are "non-solid", i.e.
     have gradient above `ε/2 + 2λα`. This invariant propagates deterministically whenever
     at most a sixth of the tests are inaccurate (`round_deterministic`).
   - *Why it propagates.* The thresholds increase by `2α` per round, so an accurate pass
     certifies solidity at the next level.
   - *Failure probability.* A binomial fraction bound gives at most
     `(1+√θ)^K θ^{K/12} ≤ e^{−13J0/48}` per round (`fraction_failure`).
   - *Union over rounds.* The union over rounds is handled by a Markov-chain health lemma
     over IID windows (`chain_health`).
   - *Initial invariant.* The initial invariant holds with probability `1 − e^{−J0/12}`
     over the seed.

Median-of-means, centered clipping and the masked-chain lower-bound instance are standard
ingredients. The new ingredients are:

- the combination that keeps the main term free of `log(1/δ)`, which is the multiscale
  catastrophe accounting with scale-dependent Chernoff counts;
- the margin-ladder selection, whose cost is only `(1 + σ²/ε²)·ℓ·polyloglog`.

## Comparison with prior work (bounded-variance, single-output, high probability)

| Result | Oracle calls for `P(‖∇f(x̂)‖ ≤ ε) ≥ 1−δ` |
|---|---|
| Ghadimi–Lan 2-RSG (SIAM J. Optim. 2013, §2.2), bounded variance | `log(1/δ)·(LΔ/ε²)(1+σ²/ε²)`, plus a `σ²/(δε²)`-type post-selection term from Chebyshev |
| Hübler–Fatkhullin–He, [arXiv:2410.13849](https://arxiv.org/abs/2410.13849) Thm 4 / Cor 5 (normalized SGD), retuned | `(LΔ/ε²)(1+σ²/ε²)·log(1/δ)`, for average-of-iterates (not a single output) |
| Clipped/normalized SGD analyses: Nguyen et al. NeurIPS 2023 ([arXiv:2304.01119](https://arxiv.org/abs/2304.01119)) Thm 5.1; Fradin et al. [arXiv:2512.18713](https://arxiv.org/abs/2512.18713) §6 | multiplicative `polylog(T/δ)` |
| Cutkosky–Mehta, NeurIPS 2021 (clipped normalized SGD with momentum); Sadiev et al., ICML 2023 (clipped SGD) | multiplicative `polylog(T/δ)` |
| Liu et al. ICML 2023; Li–Orabona 2020 | additive `log(1/δ)`, but only under sub-Gaussian noise |
| **This work** | `(1+σ²/ε²)(LΔ/ε² + ℓ log³(2+ℓ)) + √(LΔ)ℓ/ε` |

**How the main term compares.**

- The prior bounded-variance bounds multiply the main term `(LΔ/ε²)(1+σ²/ε²)` by `log(1/δ)`.
- Here the confidence enters only additively, through lower-order terms.
- Hübler–Fatkhullin–He (AISTATS 2025, PMLR 258) write: "we are not aware of any lower
  bounds specifying the optimal δ-dependence." Fradin et al. call optimal high-probability
  bounds an "open challenge" (p. 14). Both remarks concern heavy-tailed noise with a
  bounded `p`-th central moment, `p ∈ (1, 2]`.
- This work answers the question in the bounded-variance case `p = 2` only, up to the
  gaps stated above. The heavy-tailed case `p < 2` is not addressed.

**What the lower-bound side adds.**

- The masked-chain lower bound of Arjevani et al. (Math. Program. 2023) is stated for
  constant success probability and expected accuracy.
- Its extension to every success level `1 − δ ≤ 3/4` is routine, because failure
  probability `≥ 1/4 > δ` already rules out success.
- What is new on this side is only the formal combination with the two-point
  `σ² log(1/δ)/ε²` term into one budget that pairs with the upper bound.

## How the result meets the task requirements

- **Important, popular setup.** The question is high-probability stationarity of
  stochastic first-order methods for smooth nonconvex objectives under bounded variance:
  the standard model of Ghadimi–Lan and Arjevani et al. No assumption is added.
- **Upper and lower bound in the repository framework.** The upper bound is a
  `Convergence` theorem (`Template`). The lower bound is a `NonConvergence` theorem
  (`TemplateLowerBound`). They use the same oracle model (IID unbiased samples with
  variance `≤ σ²`) and the same criterion (`P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ` for one measurable
  output). The lower-bound class is a high-dimensional Euclidean subclass of the upper-bound
  class.
- **Near-tight closure.** The pair is tight up to constants in the δ-free regime. Outside
  it, the gaps are exactly those listed under "Matching lower bound".
- **Class-level result.** The setup has no `allowedAlgorithm` restriction. The lower bound
  holds for every randomized algorithm, and the upper bound exhibits one algorithm.

## Limitations

- **Polyloglog gap.** The confidence term carries `log³(2 + log(1/δ))`.
  - A doubling-ladder variant would give `log²`.
  - Whether any `polyloglog` factor is necessary is open.
  - Quantile-PAC bandit results suggest some loss may be intrinsic to selection. This is
    analogy only and is not proved here.
- **Corner term.** The term `√(LΔ)·ℓ/ε` exceeds the lower bound when `σ ≲ ε` and
  `log(1/δ) ≳ √(LΔ)/ε`. It comes from the pilot batch needed to make the multiscale
  catastrophe counts small. Logarithmic weights in the count allocation would replace it
  by `√(LΔ)ℓ/(ε log(…))`, but not remove it.
- **Constant.** The universal constant `2^71` is very loose. It was chosen for a one-line
  formula and simple proofs.
- **Known parameters.** The algorithm uses `L`, `Δ`, `σ`, `ε` and `δ`. It is not
  adaptive.
- **Lower-bound class.** The lower bound is proved on a high-dimensional Euclidean
  subclass, with `d` polynomial in `LΔ(1+σ²/ε²)/ε²` and `ε² ≤ LΔ/2^54`. This subclass is
  contained in the upper-bound class.
