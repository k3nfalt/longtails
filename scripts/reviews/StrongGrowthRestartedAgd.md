# Restarted AGD under strong growth and Lipschitz Hessians

[`result`](../../LongTails/Theorems/StrongGrowthRestartedAgd.lean) proves that a mini-batched, movement-restarted AGD with validation ([algorithm](../../LongTails/Algorithms/StrongGrowthRestartedAgd.lean)) returns a point with `∫‖∇f(out)‖ dP ≤ ε`. The objective is any `C²` function on a finite-dimensional space with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian and `f(x₀) − inf f ≤ Δ`. The oracle is i.i.d., unbiased and satisfies strong growth, `E‖g−∇f‖² ≤ (κ−1)‖∇f‖²`. The theorem assumes `4⁸ρε ≤ L²` ([setup](../../LongTails/Setups/StrongGrowthHessianLipschitz.lean)). The output is the first validated candidate, not the last iterate.

**Complexity.** The proved budget is `R·N₁·(K+1+m)·⌈800κ⌉`, where `K ≈ (L²/ρε)^{1/4}`, `N₁ ≈ 1+Δ√ρ/ε^{3/2}`, and `R` and `m` are logarithmic. Validity gives `Δ√ρ/ε^{3/2} ≤ LΔ/ε²`. With `ℓ = log(2 + LΔ/ε² + L²/(ρε))`, the budget is

`O( κ ℓ (1 + Δρ^{1/2}ε^{-3/2}) ((L²/(ρε))^{1/4} + ℓ) )`,

so the leading term is `κ L^{1/2}ρ^{1/4}Δ ε^{-7/4} ℓ`. The case `ρε > L²/4⁸` is covered by substituting `L' = 256√(ρε)`, which gives `O(κℓ(1+Δ√ρ/ε^{3/2}))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SGD under strong growth: Vaswani–Bach–Schmidt, AISTATS 2019, [Thm 3](https://arxiv.org/abs/1810.07288) (`min_i E‖∇f‖² ≤ 2κLΔ/k`). A uniformly random iterate plus Jensen gives the same criterion. Direct competitor. | `O(1 + κLΔ/ε²)` → `O(κℓ(1+Δ√ρ/ε^{3/2})((L²/ρε)^{1/4}+ℓ))` | The factor `(ρε/L²)^{1/4}ℓ` is a gain when `Δ ≥ ε^{3/2}/√ρ` and `ℓ ≪ (L²/ρε)^{1/4}`. For example, with `L,ρ,Δ,κ` fixed and `ε→0`, the speedup is `≍ ε^{-1/4}/log(1/ε)`. | None | None (both give expected gradient norm of a selected point). | Adds the Hessian-Lipschitz assumption and one log factor. Worse when `LΔ/ε² ≲ ℓ(L²/ρε)^{1/4}` or `ρε ≳ L²`. The constant is about `2·10¹¹`. |
| Restarted AGD: Li–Lin, ICML 2022 / JMLR 2023, [Thm 1](https://arxiv.org/abs/2201.11411). Special case `κ=1` only, where the oracle is exact a.s. | `O(L^{1/2}ρ^{1/4}Δε^{-7/4})` → `O(L^{1/2}ρ^{1/4}Δε^{-7/4}ℓ + ℓ²(1+Δ√ρ/ε^{3/2}) + ℓ(L²/ρε)^{1/4})` | Worse: an extra factor `ℓ` plus additive terms. | Exact gradients → stochastic oracles with `κ>1` (a nested extension). | Deterministic `‖∇f(ŷ)‖ ≤ ε` → only in expectation. | Loses a log and gives a weaker output guarantee on the overlap. |
| Stochastic nonconvex acceleration with bounded variance (Cutkosky–Mehta ICML 2020; Patitucci–Jiang–Mokhtari [2510.03167](https://arxiv.org/abs/2510.03167)). They require `σ² < ∞`. | Not comparable | Not comparable. Strong growth gives no finite `σ`. If gradients are bounded by `G`, the `σ²ε^{-7/2}` term becomes `κG²ε^{-7/2}`, which is worse. | Incomparable classes (additive vs. relative noise). | — | I did not re-verify those theorem statements. |

**Reduction check.** Plugging mini-batches into the inexact restarted AGD of Yang–Luo–Li–Jordan ([2307.00126](https://arxiv.org/abs/2307.00126), Thm 3.4) requires an *absolute* error `σ = ε²` with respect to the squared norm. Under strong growth, a batch would need about `κ‖∇f‖²/ε⁴` samples, and `‖∇f‖` along the trajectory is not uniformly bounded. That is worse than SGD. I found no analysis of nonconvex `ε^{-7/4}` methods with relative gradient errors that could be combined with median-of-means batching. So the missing step is supplied by the new pathwise per-eigencoordinate Lyapunov/martingale analysis together with validation. Proof ancestry: Li–Lin supply the movement-restart scheme and the weighted-average certificate. Yang et al. show tolerance only to absolute errors.

**Search coverage.** The searches ran on 2026-11-10 and covered arXiv, PMLR, JMLR, NeurIPS and ICLR: strong growth/interpolation acceleration, relative or multiplicative noise, and inexact nonconvex AGD. Results on strong-growth acceleration ([2404.02378](https://arxiv.org/abs/2404.02378)) are convex. AGNES ([2302.05515](https://arxiv.org/abs/2302.05515)) is also convex. The nonconvex AGNES extension ([ICLR 2025](https://arxiv.org/abs/2410.08395)) relies on PL-type geometry. None of these gives a stationarity rate for this class. I did not verify Roy et al. (NeurIPS 2020) in detail. The result was introduced in commit `ed0d23cb` on 2026-11-10. The companion note has two discrepancies:
- It states a squared log factor on the leading term, but `m` is additive to `K`, so only one log multiplies it.
- Its GLM example gives `κ ≤ n·max‖aᵢ‖²/σ_min(A)²`, which is at least `n` because `σ_min(A)² ≤ ‖A‖_F²/n`. For that finite sum, full-gradient Li–Lin, costing `n·L^{1/2}ρ^{1/4}Δε^{-7/4}`, is already at least as good.

**Conclusion**

**Yes. Under strong growth with a Lipschitz Hessian, the proved total complexity improves on SGD's `ε^{-2}` to `ε^{-7/4}`, up to one logarithm.**

The strongest applicable baseline for this oracle class is SGD under strong growth (Vaswani–Bach–Schmidt, Thm 3):

| | oracle calls for `E‖∇f(out)‖ ≤ ε` |
|---|---|
| SGD | `κLΔ/ε²` |
| this result | `κL^{1/2}ρ^{1/4}Δε^{-7/4}·log(2+LΔ/ε²+L²/ρε)` + lower-order terms |

The gain needs `Δ ≥ ε^{3/2}/√ρ` and `(L²/ρε)^{1/4} ≫ log(·)`. Its cost is an extra Hessian-Lipschitz assumption and a constant of about `10¹¹`. At `κ=1` it loses a log to Li–Lin.

Mini-batching existing inexact restarted AGD does not reproduce the bound, because that analysis needs absolute `ε²` errors. My search found no prior stochastic `ε^{-7/4}` guarantee under strong growth. That supports priority, but it does not prove it. Motivation is a real caveat: nonconvex strong growth forces every sample gradient to vanish at every stationary point. The note's GLM example also gains nothing over full-gradient restarted AGD.

The claimable contribution is the first verified accelerated stationarity bound for relative-variance stochastic gradients, with a gain of `ε^{-1/4}` over SGD up to logarithms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
