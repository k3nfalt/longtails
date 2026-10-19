# QuantileRemainderMinimaxConvex: novelty assessment

[`result`](../../LongTails/Theorems/QuantileRemainderMinimaxConvex.lean) proves the following. Take an `L`-smooth convex `f` on `ℝᵈ` with a minimizer within `R` of `x0`. Sample the oracle IID, and let each noise coordinate's law split as `S + A`: `S` is reflection-symmetric, `A` is centered with `∫z²dA ≤ M`, and `P(|noise| > r) ≤ 1/64`. No density or noise moments are assumed. Under these conditions, the projected accelerated method with characteristic-function batch estimates ([setup](../../LongTails/Setups/QuantileSymmetricRemainderConvex.lean), [algorithm](../../LongTails/Algorithms/CharacteristicGradient.lean)) returns a last iterate with `E[f(x_N) − f(xstar)] ≤ ε`.

**Proved budget.** The budget is `N·K` raw oracle calls, with `N` iterations and `K` calls per iteration. Expanded, it is

`O([1 + √(LR²/ε) + dR²(LR+r)²/ε² + d²M²R⁴/ε⁴] · log(2 + √d R(LR+r)/ε + dMR²/ε²))`,

where `d` is the dimension, `L` the smoothness constant, `R` the initial distance bound, `r` the 63/64 noise quantile, `M` the second-moment bound on the asymmetric remainder, and `ε` the target expected objective gap. The domain is `d ≥ 1`, `L,R,r,ε > 0` and `M ≥ 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Puchkin–Gorbunov–Kutuzov–Gasnikov, [AISTATS 2024 / arXiv 2311.04161 v2](https://arxiv.org/abs/2311.04161): Thm 5.7 (eq. (117)) + Lemma 4.5 → Cor 5.8, clipped-SSTM with SMoM. **Special-case baseline:** it needs a density and the convolution tail bound `s^{*k}(u) ≤ Bk/(k^{(β+1)/β}+|u|^{1+β})` with `β ≥ 1`. | With θ fixed, `b = O(C/n)`, `C ≍ √d M`, `σ² ≍ d`, so it costs `Õ(√dMR/ε · (√(LR²/ε) + dR²/ε²))`, i.e. `Õ(d^{3/2}MR³/ε³)`, with log(1/δ) factors and constants depending on `B,β,θ` (the paper states `Õ(ε⁻³)` after Cor 5.4) → `Õ(d²M²R⁴/ε⁴)` here | **Worse on the overlap** by a factor of about `√d MR/ε` (up to logs and `B,β` constants) whenever `ε ≤ √d MR` | Density + convolution tail with `β ≥ 1` → a single quantile. Newly covered: atomic noise, and symmetric backgrounds with no positive moment (e.g. density `∝ 1/((e+|z|)log²(e+|z|))`). Their class sits inside this one with `r = (128B/β)^{1/β}`, since antisymmetric parts carry no mass on symmetric sets. | None. Their guarantee is high-probability for the last iterate; this one is in expectation. | Expected rather than high-probability accuracy. The `ε` exponent is worse on the overlap. The algorithm needs `d,L,R,r,M` |
| Same paper, Prop 4.1 + Thm 5.7 (median estimator). **Restricted to `M = 0`** and density tails `p(u) ≤ B/(1∨|u|^{β+1})` | `Õ((1/β)(√(LR²/ε) + d(1∨(4B/β)^{2/β})R²/ε²))` → `O((√(LR²/ε) + dR²(LR+r)²/ε²)·log(2+√dR(LR+r)/ε))` | None: same `ε⁻²` order. Here the variance scale becomes `(LR+r)²` and there is an extra log | Density with polynomial tail → quantile only | None (high-probability → expectation) | Extra `L²R²` term and an extra log factor |

**Reduction check and proof ancestry.** The companion note itself sketches a reduction that gives the same order: Gaussian smoothing, coordinate medians of `O(log)` samples, clipping, and then biased accelerated SGD. Its sketch uses the CDF comparison behind Puchkin's Lemma A.1, with the quantile replacing the tail bound. I did not fully verify this reduction, but its steps are standard. The construction and analysis are inherited too: the product-series estimator comes from Chopin–Crucinio–Singh ([Biometrika 2025, eq. (4)](https://arxiv.org/abs/2403.20313)), and the accelerated method is a biased-oracle analysis. The only genuinely new mechanism is the remote-shell `Ω(d²M²R⁴/ε⁴)` lower bound. That bound is `oracle_complexity_lower` in [QuantileMinimax.lean](../../LongTails/Proofs/QuantileMinimax.lean). It is not part of `result`, and I did not audit it.

**Search coverage.** On 2026-10-18 UTC I read the Puchkin et al. v2 full text (Assumption 2.1, Prop 4.1, Lemma 4.5, Cor 5.4/5.8, eq. (117)). I also checked [Armacki et al. 2410.13954](https://arxiv.org/abs/2410.13954), whose asymmetric mixtures converge only to a neighbourhood. Beyond that, I ran web searches for 2024–2026 work on symmetric-plus-remainder noise and lower bounds, without a systematic forward-citation crawl. I found no published lower bound or quantile-only upper bound for this class. The theorem was introduced in commit 5e5e731 (2026-10-18 22:43 UTC). The theorem's name says "Minimax", but the formal statement is only the upper bound. The companion note correctly disclaims novelty for the upper bound.

**Conclusion**

**The theorem itself proves no faster rate; what it adds is broader scope, paid for with a worse rate where the classes overlap.** The strongest baseline is Puchkin et al.'s Corollary 5.8. On noise satisfying their density and convolution-tail conditions, it already does better:

| | Oracle calls |
|---|---|
| Puchkin et al. (their subclass, high-probability) | `Õ(d^{3/2}MR³/ε³)` |
| This theorem (in expectation) | `Õ(d²M²R⁴/ε⁴)` |

What the theorem gains is scope. It drops the density and tail-decay requirements and keeps only a 63/64 quantile. This covers atomic noise and symmetric backgrounds with no finite positive moment, which no checked published theorem handles. The verified mixture example shows that a symmetric log-tailed background plus a small centered two-point remainder fits every remaining assumption.

The scope extension is limited, though. The upper bound comes from known components: a known estimator plus biased acceleration, and the note's own smoothing–median–clipping sketch also reaches this order. The bound looks like the right price for the broader class only because of the separate lower-bound lemma, which is not part of the selected theorem. My literature search found no prior quantile-only guarantee, but it does not establish priority.

What can be claimed: a formal `ε⁻⁴` upper bound for a strictly broader moment-free class, worse than Puchkin et al. wherever their assumptions hold.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
