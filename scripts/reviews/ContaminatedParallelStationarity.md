# Novelty review: ContaminatedParallelStationarity

[`result`](../../LongTails/Theorems/ContaminatedParallelStationarity.lean) gives a deterministic elapsed-time deadline. By that deadline, honest workers on a complete point-to-point finite-bit network ([setup](../../LongTails/Setups/DistributedContaminatedSmoothNonconvex.lean), [algorithm](../../LongTails/Algorithms/ContaminatedParallelDescent.lean)) return one point `X` with `Pr(‖∇F(X)‖ > ε) ≤ δ`. Here `F = n⁻¹Σᵢfᵢ` has an `L`-Lipschitz gradient, and each worker's samples are IID from the Huber mixture `(1−ηᵢ)μᵢ + ηᵢνᵢ`, where `νᵢ` is arbitrary.

**Parameters.** `Δ` is the initial gap, `σᵢ` the clean noise level, `ηᵢ ≤ 1/16` the public contamination rate, `hᵢ` the time per sample, `ℓ, b` the latency and per-bit cost, and `d` the dimension. All of these, plus `x₀`, are given to the algorithm. The theorem requires `ε ≥ 2¹⁸ n⁻¹Σᵢσᵢ√ηᵢ` and `0 < δ < 1`. Its budget simplifies to

`T = O( [1 + LΔ/ε² + (1+log(1/δ))·min{1+LΔ/ε², 1+log(1/δ)}]·(maxᵢhᵢ + Σᵢhᵢσᵢ²/(n²ε²)) + (1+LΔ/ε²)·[(1+log n)maxᵢhᵢ + ℓ + b(1+⌈d/n⌉log(2+nd))] )`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, Leon SGD, [Thm 1.7, arXiv v1, 21 Mar 2026](https://arxiv.org/abs/2603.20735). *Applies only when η=0 and σᵢ≡σ; uses a bandwidth-graph model.* | `O((1+LΔ/ε²)·max{d/w̄, maxhᵢ, σ²·avg(h)/(nε²)})` for `E‖∇F‖² ≤ ε²` → `T` | Not comparable: the network units differ (min-cut bandwidth vs. finite-bit links with latency `ℓ`). Leon also gives no `δ`-guarantee, and Markov conversion costs a `1/δ` factor. | Clean unbiased oracle → Huber contamination with heterogeneous `σᵢ,ηᵢ` and pooled `Σhᵢσᵢ²` | Expected squared norm → tunable high probability with one returned point | Accuracy floor `ε ≳ n⁻¹Σσᵢ√ηᵢ`; complete network only; extra `K·log n·maxhᵢ` pilot term; all leaf points stored |
| [FiniteBitLeon](../../LongTails/Theorems/FiniteBitLeon.lean) (repository, earlier on 2026-11-19), boosted 2-RSG-style with `O(log 1/δ)` restarts and robust validation ([Ghadimi–Lan, Thm 2.4](https://arxiv.org/abs/1309.5549)). *Applies only when η=0.* | `O((1+log(1/δ))·(1+LΔ/ε²)·[maxhᵢ + σ²Σhᵢ/(n²ε²) + ℓ + b(1+⌈d/n⌉log(2+nd))])` plus validation → `T` | A factor `log(1/δ)` is removed from the leading term when `log(1/δ) ≤ √(LΔ)/ε`. For `log(1/δ) ≥ LΔ/ε²` the bounds have the same order. | The same as row 1, on the same network model | Expected squared norm → high probability, without a multiplicative `log(1/δ)` in this regime | `(1+log n)maxhᵢ` per step instead of `maxhᵢ` |
| Robust minibatch descent with a union bound: a robust mean estimate (bounded second moment, `η`-contamination, error `σ√η + σ√(log(1/δ')/N)`) at confidence `δ' = δ/K` at every step, with real vectors. *Check with n=1, h=1.* | `O((1+LΔ/ε²)(1 + σ²log(LΔ/(ε²δ))/ε²))` samples → `O((1+LΔ/ε²+log²(1/δ))(1+σ²/ε²))` | A factor `log(LΔ/(ε²δ))` is removed from the `σ²LΔ/ε⁴` term when `log(1/δ) ≤ √(LΔ)/ε` | None at n=1 | None (both give a single point with high probability) | None at n=1 beyond constants such as `2¹⁸` |
| [Hübler–Fatkhullin–He, Thm 4 / Cor 5, AISTATS 2025, arXiv v3](https://arxiv.org/pdf/2410.13849v3): centralized NSGD, which tolerates biased estimators with bounded conditional `E‖g−∇F‖`. *Applies at n=1 only, combined with a robust estimator.* | With the steps retuned to `η≈ε/(L log(1/δ))`: `O((LΔ log(1/δ)/ε²)(1+σ²/ε²))` → `O((LΔ/ε²+log²(1/δ))(1+σ²/ε²))` | A factor `log(1/δ)` on the leading term when `log(1/δ) ≤ √(LΔ)/ε` | None | Weighted-average gradient norm → one selected point | Under contamination, Thm 4 needs a bounded conditional `E‖g−∇F‖`. A failed robust estimate with an infinite-mean `νᵢ` breaks this unless it is safeguarded, which I did not check. Their Cor 5 tuning gives `log⁴(1/δ)` |

**Standard-reduction check.** Composing known tools (robust mean estimation, normalized descent, a union bound or restarts) reproduces the result up to an extra factor `log(K/δ)` or `log(1/δ)` on the sampling term. No exact reduction to the selected bound was found. Two new mechanisms appear. The first is a confidence allocation over the four-ary coding tree, with node precision `8(1+j)+2⌈q·min(1,u²/K₀)⌉`, that makes failure cost additive. The second is local clipping that keeps the pooled scale `Σhᵢσᵢ²` while paying only one aggregate per node. The multiscale modular coding is proof ancestry from the repository's [FiniteBitLeon](../../LongTails/Theorems/FiniteBitLeon.md). The note itself sketches an unchecked real-vector alternative: localized normalized descent with `O(K)` steps for `q ≤ √K`. If it works, the remaining gain shrinks to removing an `O(log K)`-bit range overhead from the network term.

**Search coverage.** On 2026-11-19 I searched arXiv, NeurIPS, ICML and AISTATS sources on the following topics:
- high-probability nonconvex SGD: Cutkosky–Mehta 2021; Nguyen et al. 2023; Hübler et al.; [Fradin et al., arXiv 2512.18713 v2](https://arxiv.org/abs/2512.18713), which uses mean-squared-smoothness/variance-reduction assumptions and does not apply here;
- Huber or contamination-robust SGD: [Merad–Gaïffas, TMLR 2024](https://arxiv.org/abs/2309.17316), which gives only an asymptotic nonconvex localization; outlier-robust stationarity work by Diakonikolas and coauthors, which uses strong contamination on finite datasets and is centralized;
- Byzantine distributed SGD, which concerns worker-level corruption and is a different model.

I found no prior per-sample Huber result for a distributed nonconvex problem. I did not read the Gong–Sellke and Chaudhuri et al. papers that the companion note cites. The note's comparisons agree with the Lean statement. Its "same order as constant confidence" claim holds only for `log(1/δ) ≤ √(LΔ)/ε`. The theorem was introduced in commit `c0f9420d` (2026-11-19). No subsequent work was found.

## Conclusion

**It does improve complexity, but only by logarithmic factors in confidence. The more substantive part is the combined setting.**

On the clean single-machine overlap, the strongest baselines are a robust minibatch descent with a union bound, and NSGD (Hübler et al., Thm 4) fed by a robust estimator. Both lose a multiplicative logarithm:

| | samples, n = 1 |
|---|---|
| union-bound robust descent | `(LΔ/ε²)(1+σ²/ε²)·log(LΔ/(ε²δ))` |
| this result | `(LΔ/ε² + log²(1/δ))(1+σ²/ε²)` |

The gain holds when `log(1/δ) ≤ √(LΔ)/ε`. Once `log(1/δ) ≥ LΔ/ε²`, the two have the same order.

In terms of scope, no checked work combines per-sample Huber contamination with heterogeneous rates, nonconvex averaged objectives with unbounded local disagreement, and an elapsed-time bound for a finite-bit network. Robust mean estimation, normalized descent and the repository's multiscale coding each supply known pieces. The note's own real-vector localization argument, which I did not check, may already recover `O(K)` steps.

The claimable contribution is a high-confidence, contamination-robust elapsed-time bound whose confidence cost is additive in a stated regime. This saves a `log(K/δ)` factor over direct compositions. The gain is real but logarithmic, and it is assembled from established mechanisms.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
