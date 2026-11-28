# Novelty assessment: HeavyTailedHighProbabilityStationarityUpperBound

The [theorem](../../LongTails/Theorems/HeavyTailedHighProbabilityStationarityUpperBound.lean) applies to [setup](../../LongTails/Setups/HeavyTailedHighProbabilityStationarity.lean) and [algorithm](../../LongTails/Algorithms/HeavyTailedHighProbabilityStationarity.lean). It concerns an `L`-smooth function `f` that is bounded below, on any separable Hilbert space, with IID unbiased oracles whose central `p`-th moment is at most `σ^p` for `p ∈ (1,2]`. It constructs a two-phase method (robust normalized SGD, then clipped-test ladder selection) whose single measurable output satisfies `P(‖∇f(x̂)‖ ≤ ε) ≥ 1−δ`.

**Selected complexity** (from the Lean budget, `0<δ≤1/4`):

`N = O( (1 + (Cσ/ε)^{p/(p−1)})·(LΔ/ε² + log(16/δ)·log^{2+2/p}(2+log(16/δ))) + √(LΔ)·log(16/δ)/ε )`, with `C = 2^45`.

Here `Δ ≥ f(x₀) − inf f`, `ε` is the gradient-norm accuracy and `δ` is the failure probability. The constant `C^{p/(p−1)}` is not universal as `p → 1`. The updates use `L, Δ, σ, p, ε, δ`.

Throughout, write `s₀ = (σ/ε)^{p/(p−1)}` and `ℓ = log(1/δ)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Hübler–Fatkhullin–He, AISTATS 2025 ([arXiv:2410.13849](https://arxiv.org/abs/2410.13849)), Thm 4 + Cor 5, minibatch NSGD | `O(ℓ²·LΔ/ε²·(1+(σℓ/ε)^{p/(p−1)}))` with their tuning. Retuning their eq. (19) gives `O(ℓ²(1+s₀)LΔ/ε²)`. → selected `N` | At least a factor `ℓ²` when `ℓ·log^{4}(2+ℓ) ≤ LΔ/ε²` and `ℓ ≤ (1+s₀)√(LΔ)/ε` | None (same p-BCM class) | Their bound is on the average of `‖∇f(x_t)‖` over iterates; the selected result returns one point with high probability | Larger constants. Both need `σ, p, L, Δ`. |
| Standard confidence boosting: Hübler et al. Cor 3 (expectation-optimal), then Markov, `O(ℓ)` independent runs, and median-of-means selection in the style of Ghadimi–Lan's 2-RSG ([SIOPT 2013, §2.2](https://arxiv.org/abs/1309.5549)) | `O((1+s₀)(ℓ·LΔ/ε² + ℓ²))` (my derivation) → selected `N` | Factor `Θ(ℓ)` in the same regime. When `ℓ ≫ LΔ/ε²`, the factor is `ℓ/log^{2+2/p}(2+ℓ)`. Up to constants, never worse, since `√(LΔ)/ε ≤ 1 + LΔ/ε²`. | None | None (both return one point) | The corner term `√(LΔ)ℓ/ε`. Gains are only asymptotic because of the `2^76` and `(2^45)^{p/(p−1)}` constants. |
| Nguyen et al., NeurIPS 2023 ([arXiv:2304.01119](https://arxiv.org/abs/2304.01119)) Thm 5.1. Sadiev et al., ICML 2023 ([arXiv:2302.00999](https://arxiv.org/abs/2302.00999)) Thm 3.1, bound (16). | Leading order `ε^{-(3p−2)/(p−1)}`, multiplied by `log(1/δ)` or `log(K/δ)`. Their dependence on `LΔ, σ` is worse for `p<2` (Sadiev: `(√(LΔ)σ/ε²)^{p/(p−1)}`). → selected `N` | `Ω(ℓ)` or more, plus better `LΔ` dependence for `p<2` | None | Their guarantees are for the average squared gradient norm, not a returned point | None beyond constants |
| Repository [HighProbabilityStationarityUpperBound](../../LongTails/Theorems/HighProbabilityStationarityUpperBound.lean) (2026-11-20). Special case `p = 2` only. | `(1+σ²/ε²)(LΔ/ε² + ℓ log³(2+ℓ)) + √(LΔ)ℓ/ε` → the same form for all `p` | None at `p=2` (same order) | Bounded variance → bounded central `p`-th moment, `p ∈ (1,2]` | None | Power `2+2/p ≤ 4` instead of 3 |

**Classes I excluded from the table:**
- Cutkosky–Mehta (NeurIPS 2021) bound a *raw* moment, which implies bounded gradients, so their class is narrower.
- Fradin et al. ([arXiv:2512.18713](https://arxiv.org/abs/2512.18713), Thm 6.1) add weak average smoothness (Assumption 2.6).
- Armacki et al. ([arXiv:2507.09093](https://arxiv.org/abs/2507.09093)) assume symmetric noise or use symmetrizing estimators.
- Liu–Zhou (ICLR 2025, [arXiv:2412.19529](https://arxiv.org/abs/2412.19529)) give in-expectation results only.

**Reduction check.** Standard reductions (Markov plus repetition plus selection, or the high-probability version of normalized SGD) all pay `ℓ` multiplicatively on `(1+s₀)LΔ/ε²`. The additive form needs two new ingredients:
- an effective-variance reduction to the repository's own `p=2` proof;
- bias-stable clipped tests, which keep the selection cost at `ℓ·polyloglog(ℓ)` instead of losing a factor `ℓ^{(2−p)/(p−1)}`.

**Proof ancestry.** The Phase-1 analysis and the ladder come from the repository's `p=2` result, which is unpublished. Clipping and median-of-means lemmas are classical tools.

**Search coverage.** On 2026-11-25 I searched arXiv and the web for heavy-tailed nonconvex high-probability stationarity with additive or optimal `δ`-dependence. I read the theorem statements of Hübler et al., Nguyen et al., Sadiev et al. and Fradin et al. directly. Hübler et al. say they know of no lower bound giving the optimal `δ`-dependence. I did not access ICLR 2027 OpenReview submissions. Gradient-norm results under sub-Gaussian noise are a stronger noise model, and I did not compare them exhaustively. The companion note's citations match the papers I checked. Its claimed lower-bound pairing was not audited here.

## Conclusion

**Yes: confidence enters additively, which improves the high-probability complexity by a factor of about `log(1/δ)`.**

The strongest applicable baseline is Hübler–Fatkhullin–He's expectation-optimal minibatch NSGD, boosted to a high-probability guarantee by the standard repeat-and-select reduction. Under the same p-BCM class, oracle and single-point criterion:

| | Oracle calls |
|---|---|
| Boosted baseline | `(1+s₀)(ℓ·LΔ/ε² + ℓ²)` |
| This result | `(1+s₀)(LΔ/ε² + ℓ·log^{2+2/p}(2+ℓ)) + √(LΔ)·ℓ/ε` |

Up to constants, the new bound is never worse. It is a factor `Θ(log(1/δ))` smaller when `log(1/δ)·log⁴(2+log(1/δ)) ≲ LΔ/ε²` and `log(1/δ) ≲ (1+s₀)√(LΔ)/ε`. For example, with `σ > 0` fixed, `δ = ε^{10}` and `ε → 0`, the gain is about `10·log(1/ε)`.

The gain has limits. It is asymptotic: the constants `2^76` and `(2^45)^{p/(p−1)}` are enormous and grow as `p → 1`. It needs known `σ, p, L, Δ`. It retains a corner term and a polyloglog factor whose necessity is open. At `p = 2` the result reproduces the repository's own earlier theorem, so the step beyond it is extending the additive confidence cost to `p < 2`.

The comparison establishes the gain over the checked baselines. Literature priority rests on not having found any prior additive-confidence result for heavy-tailed nonconvex stationarity, which is good evidence but not proof. The contribution that can be claimed is the first proved additive-confidence complexity for high-probability `ε`-stationarity under bounded central `p`-th moments.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
