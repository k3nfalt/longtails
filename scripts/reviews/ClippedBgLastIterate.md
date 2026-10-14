# ClippedBgLastIterate: novelty assessment

[`result`](../../LongTails/Theorems/ClippedBgLastIterate.lean) proves that, for a convex (possibly nonsmooth) `f` on a closed convex `X ⊆ ℝᵈ` with a minimizer `u`, `‖x₀−u‖ ≤ R`, and IID stochastic subgradients satisfying the Blum–Gladyshev (BG) full-moment bound `E‖g(x)‖² ≤ B²‖x−x₀‖² + G²`, the **actual last iterate** `x_T` of the [influence-clipped projected subgradient method](../../LongTails/Algorithms/TerminalClipping.lean) satisfies `P[f(x_T)−f(u) > ε] ≤ δ`. This holds whenever `(2²⁰(BR²+G²/B) log(8/δ))² ≤ Tε²`, with `B,G>0` and `0<δ<1` ([setup](../../LongTails/Setups/TerminalClippingConvex.lean)). The step and threshold use `B, G, δ, T`, but not `R` or `ε`.

**Complexity.** The run uses `T` subgradient calls and `T` projection calls:

  N = O(1 + (BR² + G²/B)² log²(1/δ) / ε²).

Here `B` is the moment-growth rate, `G` is the moment level at `x₀`, `R` is the initial distance, and `δ` is the failure probability. The bound blows up as `B→0` (`G⁴/(B²ε²)` term). Applying it to bounded-moment instances therefore needs `B ≈ G/R`, i.e. knowledge of `R`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Alacaoglu–Malitsky–Wright, [arXiv:2504.09951](https://arxiv.org/abs/2504.09951) (v1 Apr 2025, v3 26 Sep 2026; preprint), Thm 3.6 (projected Halpern, identical BG class), plus Markov | `O((BR²+G²/B)² log²((BR²+G²/B)/(εδ))/(ε²δ²))` → `O((BR²+G²/B)² log²(1/δ)/ε²)` | Factor `≈ log²(K)/(δ² log²(1/δ))`; for every `δ<1` up to universal constants. For constant `δ`, only a `log²` horizon factor | None (same class) | Expected last-iterate gap → high-probability last-iterate gap. Markov is the only checked conversion (no function-value oracle exists for selecting among repeated runs) | Loses the anytime schedule (`T` must be fixed); constants ≈2⁴⁰ versus ≈216 |
| Liu–Zhou, [arXiv:2303.12277v3](https://arxiv.org/abs/2303.12277), Thm 3 (fixed-`T` clipped SGD, `p=2`). **Special case:** `G_L`-Lipschitz `f` and central variance `σ²` | With free `β`: `O(log²(1/δ)(β+R²/β)²(G_L²+σ²)/ε²)` → the same order, using `G² = G_L²+σ²` and `B = G/β` | None: same order | BG growth (`f` may be non-Lipschitz, with moments growing in `‖x−x₀‖`) → covered; previously only uniform `G_L`, `σ` | Averaged `x̄_T` → last iterate | Their Thm 6 is genuinely `R`-adaptive (log mismatch), but for averaged output |
| Liu–Zhou, [arXiv:2312.08531v4](https://arxiv.org/abs/2312.08531) (ICLR 2024), Thm 3.5. **Special case:** sub-Gaussian noise, `M`-Lipschitz, last iterate | `O((M²+σ² log(1/δ))R²/ε²)` (`R`-tuned) → `O((M²+σ²)R² log²(1/δ)/ε²)` with `B=G/R` | Worse by a `log(1/δ)`–`log²(1/δ)` factor | Sub-Gaussian → finite second moment; Lipschitz → BG | None (both are high-probability last-iterate guarantees) | None beyond the log loss |
| Chezhegov–Parletta–Paudice–Gorbunov, [ICLR 2026](https://mlanthology.org/iclr/2026/chezhegov2026iclr-highprobability/), Thm 1. **Special case:** `L`-smooth, `α=2` | `Õ(LR²/ε + (D/ε)³)` with `D ≥ Rσ` (full `D` unverified) → `O((LR²+σ²/L)² log²(1/δ)/ε²)` (`B=√2L`, `G² = 2‖∇f(x₀)‖²+σ² ≤ 2L²R²+σ²`) | Better for `ε ≤ min(σ³/(L²R), L²R³/σ)` (ε⁻² vs ε⁻³); worse in the deterministic term (`L²R⁴/ε²` vs `LR²/ε`) | Smoothness → none needed | Their tuning uses `R₀`; this one needs `B=√2L` and a supplied `G² ≥ 2‖∇f(x₀)‖²+σ²` instead | Their method is anytime and covers α<2; this one needs a full (uncentered) moment and a fixed `T` |

**Reductions and mechanism.** Markov on the expectation result loses `1/δ²`. Repetition-plus-selection is unavailable because the oracle gives no function values. Restricting to a ball of radius `O(R)` (making `f` Lipschitz there) needs `R`, a projection onto `X ∩ ball`, and yields only averaged outputs. Under BG I found no high-probability guarantee for any output. Weighted averages concentrated at the endpoint lose the sample-size gain. The new mechanism is the observable influence-dependent threshold `min{M_t√T, M_t²/(B√T‖U_t‖)}`, which bounds late terminal martingale jumps and pays its bias from the negative distance term. Proof ancestry: the moving-comparator telescope of Liu–Zhou (2312.08531, Lemma 4.1) and standard clipping bias/variance bounds. Neither supplies the heavy-tail terminal concentration.

**Search coverage.** Searched on 2026-10-08 UTC: arXiv, ICLR 2024/2026, OpenReview, and the cited and citing literature on BG noise, clipped subgradient methods, and last-iterate high-probability bounds. The OpenReview PDF of Chezhegov et al. and the citation listing for AMW were inaccessible, so Chezhegov et al.'s full constant `D` is unverified. Parletta–Paudice–Salzo ([arXiv:2410.00573v2](https://arxiv.org/abs/2410.00573), Apr 2025, §7) explicitly leave *high-probability last-iterate rates under heavy tails* open for Lipschitz nonsmooth problems. I found no later resolution before the theorem was introduced (commit 41c2c3d, 2026-10-07). The companion note's citations match the checked statements. Its "no supplied radius" claim amounts to standard fixed-step tuning with quadratic `R`-mismatch, not distance adaptivity.

**Conclusion**

**Yes—it gives the first high-probability last-iterate guarantee I could find for nonsmooth convex problems with only second-moment, distance-growing (BG) noise.** On the identical class, the strongest baseline is the expectation-only last-iterate bound of Alacaoglu–Malitsky–Wright. Converting it to probability `1−δ` costs:

| | oracle calls |
|---|---|
| AMW + Markov | `(BR²+G²/B)² log²(K) / (ε²δ²)` |
| this result | `(BR²+G²/B)² log²(1/δ) / ε²` |

This is a gain of roughly `1/δ²` for every `δ<1`, at the cost of a fixed horizon and very large constants.

On the bounded-moment overlap (Lipschitz `f`, uniform variance), clipped SGD with an averaged output (Liu–Zhou 2023, Thm 3) already achieves the same order. There, the only gain is that the output is the last iterate rather than an average. Sub-Gaussian last-iterate results are slightly better by log factors. The method is not adaptive to `R`: it pays the usual quadratic penalty `(BR²+G²/B)²` when `B` mismatches `G/R`.

The comparison proves the δ-gain over the identical-class baseline. Priority is supported because a 2025 paper explicitly lists this question as open (for heavy tails generally) and my search found no later resolution. That search is not exhaustive. The claimable contribution is a new clipping rule and analysis giving `ε⁻² log²(1/δ)` high-probability last-iterate complexity under BG moments.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
