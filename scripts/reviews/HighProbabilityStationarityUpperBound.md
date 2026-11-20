# Novelty assessment: HighProbabilityStationarityUpperBound

The theorem proves the following for every differentiable `f` on a complete, second-countable real inner-product space ([theorem](../../LongTails/Theorems/HighProbabilityStationarityUpperBound.lean), [setup](../../LongTails/Setups/HighProbabilityStationarity.lean), [algorithm](../../LongTails/Algorithms/HighProbabilityStationarity.lean)):
- **Assumptions.** `∇f` is `L`-Lipschitz, `f(x₀) − inf f ≤ Δ`, and the oracle gives IID, jointly measurable, unbiased stochastic gradients with variance at most `σ²`. Parameters satisfy `0 < δ ≤ 1/4`.
- **Algorithm and output.** Robust normalized SGD, followed by a median-of-means "margin-ladder" selection, returns one measurable point `x̂`.
- **Guarantee.** `P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ` within the budget below.

Here `L` is the smoothness constant, `Δ` the initial gap, `σ²` the variance, `ε` the target gradient norm and `δ` the failure probability. With `ℓ = log(1/δ)`, which is `≍ log(16/δ)` because `δ ≤ 1/4`:

```
N = O( (1 + σ²/ε²)·(LΔ/ε² + ℓ·log³(2+ℓ)) + √(LΔ)·ℓ/ε )     (L, ε > 0;  Δ, σ ≥ 0;  δ ≤ 1/4)
```

This is the Lean budget `⌈2⁷¹(…)⌉₊` with the constant dropped. Below, `M := (LΔ/ε²)(1 + σ²/ε²)` is the in-expectation complexity of Arjevani et al. (Math. Program. 2023).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan 2-RSG, SIAM J. Optim. 2013 ([arXiv:1309.5549](https://arxiv.org/abs/1309.5549), Thm 4(b), eq. 2.32). Bounded variance, single output. | `O(ℓ·M + ℓ²σ²/(δε²))` → `N` | Main term loses its `ℓ` factor. Confidence term goes from polynomial `1/δ` to `(1+σ²/ε²)ℓ log³(2+ℓ)`. | None (same class) | None (both give one point with known parameters) | `N` adds `√(LΔ)ℓ/ε + ℓ log³(2+ℓ)` even when `σ ≲ ε` |
| Hübler–Fatkhullin–He, AISTATS 2025 ([arXiv:2410.13849](https://arxiv.org/abs/2410.13849) v3, Thm 4). Minibatch normalized SGD. Retuned by me: `η = ε/(Lℓ)`, `T = LΔℓ/ε²`, `B = σ²/ε²`. Their stated Cor 5 tuning gives `ℓ⁴`. Selection adds `(1+σ²/ε²)ℓ²` (median-of-means test of `O(ℓ)` sampled iterates). | Average output: `O(ℓ·M + √(LΔ)ℓ/ε)`. Single output: `O(ℓ·M + √(LΔ)ℓ/ε + (1+σ²/ε²)ℓ²)` → `N` | Factor `Θ(ℓ)` when `M ≥ (1+σ²/ε²)ℓ log³(2+ℓ)` and `M ≥ √(LΔ)ℓ/ε`. Never worse up to a universal constant, since `log³(2+ℓ) ≤ 1.6ℓ` for `ℓ ≥ log 4`. | None | Average of `‖∇f(x_t)‖` → a single returned point (also available to the baseline through the selection step above) | None. The `√(LΔ)ℓ/ε` term is shared. |
| Liu–Nguyen–Nguyen–Ene–Nguyen, ICML 2023 ([arXiv:2302.14843](https://arxiv.org/abs/2302.14843), Thm 4.1). **Applies only to sub-Gaussian noise.** | Average squared norm: `O(M + σ²ℓ/ε²)` → `N` | Not comparable as an improvement. On the sub-Gaussian subclass, Liu is better by `log³(2+ℓ)` and has no `√(LΔ)ℓ/ε` term. | sub-Gaussian noise → variance `σ²` only (heavier-tailed noise is now covered) | Average → single point | Worse on the sub-Gaussian overlap, as stated |

**Reduction check and proof ancestry.** I composed the known pieces: an in-expectation or average-iterate guarantee, plus median-of-means post-selection or per-step median-of-means gradients. Every such composition keeps `ℓ` multiplying `M`, either as `ℓ·M` or as `M·log(T/δ)`. I found no reduction that removes it.

The theorem's mechanism is different: multiscale catastrophe counting with scale-dependent Chernoff counts in Phase 1, and the margin-ladder selection in Phase 2. I checked it only through the formal statement and the budget formulas, not by re-deriving the proofs. Centered clipping and median-of-means (Lugosi–Mendelson; Minsker), normalized SGD (Cutkosky–Mehta, NeurIPS 2021; Hübler et al.) and the Ghadimi–Lan post-selection are proof ancestry. They supply ingredients, not this bound. I did not run a build or the axiom audit.

**Search coverage.** I searched on 2026-11-20, covering arXiv and ICML/NeurIPS/AISTATS/JMLR/SIAM sources up to that date. Papers checked:
- Ghadimi–Lan; Hübler et al.; Liu et al. 2023.
- Fradin–Sadiev–Condat–Richtárik ([arXiv:2512.18713](https://arxiv.org/abs/2512.18713) v2, Mar 2026): heavy-tailed noise; its high-probability rate (Thm 6.1) has a multiplicative `log(T/β)` and needs mean-squared smoothness.
- Zhu–Huang ([arXiv:2611.17736](https://arxiv.org/abs/2611.17736), 13 Nov 2026, one week before this result): the `log(1/δ)` is additive, but it assumes sub-Gaussian noise and bounded gradients.
- Wu ([arXiv:2609.30499](https://arxiv.org/abs/2609.30499), Sep 2026): its high-probability results need moments of order `p > 2`, and its tail term grows polynomially in `1/δ`.

Some theorem statements for Fradin and Wu came only from summaries of the HTML, and I did not consult the SIAM numbering of Ghadimi–Lan. The companion note's citations are consistent with what I verified. The "open challenge" quote from Fradin et al. is unverified, and Hübler's verbatim remark ("not aware of any lower bounds specifying the optimal δ-dependence") concerns `p`-th moment noise in general. The result entered the repository in commit `0da5e0ce` (2026-11-20).

## Conclusion

**Yes: under bounded variance alone, the proved complexity removes the `log(1/δ)` factor from the leading term.** The strongest applicable baseline I found is Hübler–Fatkhullin–He's normalized SGD (Theorem 4), retuned and followed by standard median-of-means selection:

| | single-output oracle calls, `ℓ = log(1/δ)`, `M = (LΔ/ε²)(1+σ²/ε²)` |
|---|---|
| best composed baseline | `ℓ·M + √(LΔ)ℓ/ε + (1+σ²/ε²)ℓ²` |
| this theorem | `M + (1+σ²/ε²)ℓ log³(2+ℓ) + √(LΔ)ℓ/ε` |

Term by term, the new bound is never worse up to universal constants. It is faster by a factor `Θ(log(1/δ))` whenever `M ≥ (1+σ²/ε²)ℓ log³(2+ℓ)` and `M ≥ √(LΔ)ℓ/ε`. For example, with `L, Δ, σ ≥ ε` fixed and `δ → 0` slowly enough that `ℓ log³ℓ ≤ LΔ/ε²`, the cost stays `O(M)` while the baseline grows like `ℓM`. Combined with the companion lower bound `Ω(M + σ²ℓ/ε²)` (high dimension, `ε² ≤ LΔ/2⁵⁴`), this is order-optimal in that regime.

It loses in two places. Under sub-Gaussian noise, Liu et al. already obtain the additive `σ²ℓ/ε²` form, without the `log³` factor or the `√(LΔ)ℓ/ε` term. For nearly noiseless oracles (`σ ≲ ε`), the confidence overhead is not shown to be necessary. All parameters `L, Δ, σ, ε, δ` must be known.

The comparison establishes the gain over every composed baseline I checked. The literature search found no earlier bounded-variance result with an additive confidence term, but a search cannot prove priority, and several recent papers were read only partly. The claimable contribution is the first verified single-output, high-probability nonconvex bound under bounded variance in which `log(1/δ)` enters only through lower-order terms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
