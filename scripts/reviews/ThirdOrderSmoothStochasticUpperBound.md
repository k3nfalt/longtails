# Novelty assessment: ThirdOrderSmoothStochasticUpperBound

[The theorem](../../LongTails/Theorems/ThirdOrderSmoothStochasticUpperBound.lean) proves that normalized SGD with two-lookahead extrapolated momentum ([algorithm](../../LongTails/Algorithms/LookaheadMomentum.lean)) returns a uniformly sampled iterate x̂ with E‖∇f(x̂)‖ ≤ ε. It covers every C³ function f on a finite-dimensional space ([setup](../../LongTails/Setups/StochasticThirdOrderSmoothNonconvex.lean)) whose gradient, Hessian and third derivative are L₁-, L₂- and L₃-Lipschitz, with f(x₀) − inf f ≤ Δ. The oracle returns IID single-query unbiased stochastic gradients with variance at most σ². The tuning uses known L₁, L₂, L₃, σ, Δ and ε.

**Proved budget** (this is the Lean budget with the constant 10⁵ suppressed; it counts every call, including the initial batch n₀ = ⌈1/γ⌉):

  N = O( 1 + σ²/ε² + L₁Δ/ε² + (Δσ²/ε³)·min{ L₁/ε, √(L₂/ε), (L₃/ε)^{1/3} } ),

valid for L₁, L₂, L₃, ε > 0 and σ, Δ ≥ 0. For fixed parameters and σ > 0 it is O(Δσ²L₃^{1/3} ε^{−10/3}).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| He, [arXiv:2412.14488](https://arxiv.org/abs/2412.14488) (v1 Dec 2024, v4 Apr 2025; preprint), Thm 2 (p = 3). Same class with L₁ and L₃, same oracle moments, same criterion and random-iterate output. | 2K calls with K ≥ ((20M₃/3ε)·ln(20M₃/3ε))^{10/3}, where M₃ = 4(Δ + 19σ² + L₁ + 4L₃² + 2) → N above | The ln^{10/3}(M₃/ε) factor is removed. Parameter dependence becomes polynomially better: Δ^{10/3}σ^{20/3}L₃^{20/3} → Δσ²L₃^{1/3}. Example with Δ = L₁ = L₃ = 1, σ² = s ≥ 1 and ε ≤ 1: (s/ε)^{10/3}·log → O(s ε^{−10/3}), a gain of order s^{7/3}·ln^{10/3}(s/ε). | Adds a min with the L₁ and L₂ regimes (He's p = 3 bound has no L₂). | Worse: He's schedules use no problem parameters; this result needs L₁, L₂, L₃, σ, Δ and ε. | He reuses one sample at both lookahead points; this result uses a fresh sample per query. His Lemma 3 bounds the noise term without mean-squared smoothness, so the difference appears minor. |
| He–Lu–Sun–Deng, [arXiv:2506.11214](https://arxiv.org/abs/2506.11214) (v2 Feb 2026; preprint), Thm 3 at α = 2 (bounded variance), p = 3 | Õ((M/ε)^{10/3}), where M is additive in Δ, σ² and L₃², with a logarithm inside the power → N | Same kind of gain as in the row above. | None for α = 2. That paper also covers heavy-tailed noise, which this result does not. | Worse: theirs is parameter-free in the updates. | Narrower noise model than their α < 2 results. |
| Cutkosky–Mehta, [ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html), Thm 3 (NIGT). Special case: Lipschitz gradient and Hessian only, i.e. no L₃. | Known parameters; average of E‖∇F‖ ≤ 27Δ^{2/7}L₂^{1/7}σ^{4/7}T^{−2/7} + 5√(ΔL₁/T) + (lower-order terms) ⇒ O(Δσ²√L₂ ε^{−7/2} + L₁Δ/ε² + …) → N | On the overlap where L₃ is also finite, ε^{−7/2} improves to ε^{−10/3} when L₃²ε < L₂³ (up to constants). Otherwise both have the same order. | Uses third-order smoothness, which NIGT cannot exploit. | None: both need known parameters and give the same output. | Requires a Lipschitz third derivative to gain. Makes two oracle calls per step instead of one. |

**Standard-reduction check.** I find the gain over He to be a constant-parameter retuning of He's estimator, of the same kind Cutkosky–Mehta used at p = 2. He's Lemma 3 already contains the third-order drift, in squared form L₃²η⁶/γ⁶ (up to constants, with momentum weight θ ≍ γ). This makes the accumulated bias of order L₃η³/γ³. Requiring that bias to be ≲ ε gives η ≍ γ(ε/L₃)^{1/3}; then γ ≍ ε²/σ² and T ≍ Δ/(ηε) give Δσ²L₃^{1/3}ε^{−10/3}. The repository's three-point Taylor cancellation and fresh-sample noise recursion are careful versions of this computation, not a new mechanism. He supplies the extrapolation weights and moment conditions (proof ancestry); Cutkosky–Mehta supply the known-parameter template.

**Search coverage (2026-11-20).** I searched arXiv and the ICML/COLT/NeurIPS proceedings for stochastic first-order methods under Lipschitz third or higher derivatives, and checked the following:
- He's theorem statements, partly through text summaries.
- Cutkosky–Mehta Thm 3, read from the PDF.
- Arjevani et al., [COLT 2020](https://arxiv.org/abs/2006.13476), Thm 3. Its lower bound, (Δσ²/ε³)·min_q (L_q/ε)^{1/q}, matches the leading term here.
- Patitucci–Jiang–Mokhtari ([arXiv:2510.03167](https://arxiv.org/abs/2510.03167)): p = 2 only.
- Yu–Xu–Gu ([NeurIPS 2018](https://arxiv.org/abs/1712.06585)): a stronger component-smoothness model.
- [arXiv:2606.05438](https://arxiv.org/abs/2606.05438) and [arXiv:2610.02791](https://arxiv.org/abs/2610.02791): deterministic only.

I found no prior log-free, known-parameter p = 3 bound with this parameter dependence. The upper bound was added at commit 84c39ef4 (2026-11-20), so all the work above is prior. The companion note's claims agree with what I checked; it already calls this half's novelty "modest."

## Conclusion

**Yes, the proved complexity is better than the best published bound for this exact setup, but the gain comes from a routine known-parameter retuning.** The closest baseline is He's multi-extrapolated momentum (Thm 2), which uses the same oracle model:

| | Calls for E‖∇f(x̂)‖ ≤ ε |
|---|---|
| He (parameter-free) | ((Δ + σ² + L₁ + L₃² + 1)/ε · log)^{10/3} |
| This result (known parameters) | 1 + σ²/ε² + L₁Δ/ε² + Δσ²L₃^{1/3}ε^{−10/3} |

The new bound drops a ln^{10/3}(1/ε) factor and replaces the polynomial blow-up in Δ, σ and L₃ with linear dependence on Δσ² times L₃^{1/3}. Its leading term matches the Arjevani et al. lower-bound expression. Through the min over the three smoothness regimes, it also contains the Cutkosky–Mehta Hessian-Lipschitz rate. The cost is that the method needs L₁, L₂, L₃, σ, Δ and ε, while He's updates need none of them. In the low-noise regime, the L₁Δ/ε² term is not competitive with deterministic ε^{−5/3} methods.

The mechanism is He's estimator tuned with Cutkosky–Mehta-style constant parameters, a few lines of algebra on known recursions. My search found no earlier statement of this sharp bound, but that does not establish priority, since a known-parameter corollary may have gone unstated. What can be claimed is an explicit, log-free, parameter-sharp upper bound for p = 3. Its main significance is as the matching half of the companion lower bound.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
