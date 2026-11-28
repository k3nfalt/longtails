# High-probability nonconvex stationarity under heavy-tailed noise: randomized lower bound

Lean: [`HeavyTailedHighProbabilityStationarityLowerBound.lean`](HeavyTailedHighProbabilityStationarityLowerBound.lean) (theorem `result`).
- Setup: [`Setups/HighDimensionalHeavyTailedHighProbabilityStationarity.lean`](../Setups/HighDimensionalHeavyTailedHighProbabilityStationarity.lean).
- Hard instances and assembly: [`Proofs/HeavyTailedHighProbabilityLower.lean`](../Proofs/HeavyTailedHighProbabilityLower.lean).
- Coin-noise moment lemma: [`Proofs/HeavyTailedHighProbabilityMoments.lean`](../Proofs/HeavyTailedHighProbabilityMoments.lean).

The matching upper bound is [`HeavyTailedHighProbabilityStationarityUpperBound`](HeavyTailedHighProbabilityStationarityUpperBound.md).

## Setup

The class is the high-dimensional Euclidean subclass of the heavy-tailed high-probability setup. The instance class, oracle model and success criterion are identical to the upper bound's, because `admissible` and `successful` delegate to the general setup through `toGeneral`:
- `E = EuclideanSpace ℝ (Fin d)`, with sample space `ℝ`;
- `f` is `L`-smooth with `f(x0) − inf f ≤ Δ`;
- the oracle is IID, unbiased, and has central p-th moment at most `σ^p`, with `p ∈ (1,2]`;
- success means `P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ`.

`valid` requires:
- `L > 0`, `1 < p ≤ 2`, `σ ≥ 0`, `ε > 0` and `0 < δ ≤ 1/4`;
- `LΔ ≥ 2^54 ε²`;
- dimension `d ≥ 2^130 (1 + LΔ(1 + (σ/ε)^{p/(p−1)})/ε²)^4`.

For every `p ∈ (1,2]` and every other parameter choice, a large enough `d` makes the valid set nonempty.

## Result

Write `s′ = (σ/(2^12 ε))^{p/(p−1)}`. For every randomized algorithm and every budget

```
N ≤ ⌊((1 + s′)·LΔ/ε² + s′·log(1/(4δ))) / 2^55⌋,
```

including `N = 0`, there is an admissible instance on which the algorithm fails: `P(‖∇f(x̂)‖ ≤ ε) < 1 − δ`. The instance may depend on the algorithm but not on its seed.

## Construction

**Main term `(1+s′)LΔ/ε²`.** This term uses the repository's masked Carmon chain from the ABC-noise lower bound (PR #185, `AbcLowerAssembly`, `HighProbabilityChainFailure.exists_hp_failure`).
- **Parameters.** The chain is instantiated with `A = B = 0` and `C = 1740²ε²(1 + t)`, where `t = (σ^p/(2(1740ε)^p))^{1/(p−1)}`.
- **Reply.** The ABC reply is `knownPart + coin_q·(∇ − knownPart)`, with coin `1/q` with probability `q = 1/(1+t)` and 0 otherwise, and `‖∇ − knownPart‖ ≤ 1740ε`.
- **New lemma.** `coin_moment` shows `E|coin_q − 1|^p ≤ 2t^{p−1}` for every `p ∈ (1,2]`. So the central p-th moment of the reply is at most `2t^{p−1}(1740ε)^p = σ^p`, and the hard instance is admissible for the heavy-tailed model.
- **Failure.** The chain fails with probability at least `1/4 > δ` within `⌊LΔ(1 + C/ε²)/(2^53ε²)⌋ ≥ ⌊(1+s′)LΔ/(2^53ε²)⌋` queries.

**Confidence term `s′·log(1/δ)`.** This term uses PR #229's two-point instance `f_± = (L/2)⟨e, x−x0⟩² ± 2ε⟨e, x−x0⟩`. The two gradients differ by `4ε`, so no point is ε-stationary for both.
- **Reply.** The reply reveals the sign only with probability `r = 1/(1+t₂)`, with `t₂ = (σ^p/(2(2ε)^p))^{1/(p−1)}`; its central p-th moment is at most `σ^p` by the same lemma.
- **Failure.** If no query reveals, the two transcripts coincide. This happens with probability `(1−r)^N ≥ e^{−N/t₂} > 2δ` whenever `N ≤ t₂·log(1/(4δ))/2`, and one of the two signs then fails with probability at least `δ`.
- **Reuse.** The PR #229 lemmas are reused verbatim, through the parameter map `pointParams` (`σ₂ = 2ε√t₂`).

The two cases are combined exactly as in PR #229 (`budget_split`).

## What is new and what is not

**Not new.**
- The masked-chain and rare-reveal mechanisms are standard (Arjevani et al., Math. Program. 2023; Zhang et al., NeurIPS 2020, Thm 6; repo PRs #185 and #229).
- The rare-reveal instance is essentially the erasure family used for convex heavy-tailed problems in [arXiv:2610.00260](https://arxiv.org/abs/2610.00260).
- Extending constant-probability lower bounds to every `δ ≤ 1/4` is routine.

**New.**
- The p-th-moment admissibility of both hard oracles (`coin_moment`, `chain_moment`, `point_moment`), which covers every `p ∈ (1,2]`. Zhang et al.'s instance bounds a raw moment and needs a gradient-size condition.
- The combined single budget `Ω((1+s′)LΔ/ε² + s′log(1/δ))` against all randomized algorithms. It pairs with the upper bound to give the first high-probability characterization under heavy tails.

## Tightness regime

Write `T = LΔ/ε²`. If `s′ ≥ √T`, the upper bound's corner term `√T·log(16/δ)` is at most a constant times `s′·log(1/δ)`. The pair then agrees for every `δ ≤ 1/4`, up to `log^{2+2/p}(2+log(1/δ))` and the rescaling of `σ/ε`. For fixed `σ > 0` this holds for all sufficiently small `ε`. At constant `δ`, this lower bound also gives the in-expectation-order lower bound `Ω((1+s′)T)` for the central-moment class against all randomized algorithms. Zhang et al. (Thm 6) prove that order for raw moments, under a gradient-size condition.

## Gap to the upper bound

The upper bound is dimension-free. This lower bound needs `d` polynomial in `LΔ(1 + s′)/ε²`, as the other chain lower bounds in the repository do.

The upper bound is `O((1+s)(LΔ/ε² + ℓ log^{2+2/p}(2+ℓ)) + √(LΔ)ℓ/ε)`, with `s = (2^45σ/ε)^{p/(p−1)}` and `ℓ = log(16/δ)`. The remaining gaps are:
- **Rescaling of σ/ε.** `s/s′ = (2^57)^{p/(p−1)}`, a universal rescaling inside the power.
- **Selection factor.** `log^{2+2/p}(2+ℓ)` on the confidence term.
- **Low-noise regime.** For `σ ≪ ε`, the upper confidence term is `ℓ·polylog(ℓ)`, versus `s′ℓ` here. A swap construction (not formalized) gives `Ω(ℓ/log(ε/σ))` in that regime.
- **Corner term.** `√(LΔ)ℓ/ε`, relevant only when `δ ≤ exp(−c(1+s)√(LΔ)/ε)`.

## How the result meets the task requirements

- **Popular setup.** Heavy-tailed nonconvex stochastic optimization in high probability, the open question of Hübler–Fatkhullin–He (AISTATS 2025, §3.2) and Fradin et al. (AISTATS 2026, §6).
- **Framework.** A `NonConvergence` theorem in `TemplateLowerBound`, proved at every componentwise budget below the stated one.
- **Same model as the upper bound.** It uses the same oracle model and criterion as the upper bound, on a high-dimensional subclass.
