# Novelty review: accelerated proximal STORM under strong growth and mean-squared smoothness

[`result`](../../LongTails/Theorems/ProximalStormStrongGrowth.lean) proves an expected last-output bound `E[f(y_K)] − f(x⋆) ≤ ε` ([setup](../../LongTails/Setups/StrongGrowthMeanSquaredSmoothConvex.lean), [algorithm](../../LongTails/Algorithms/ProximalStorm.lean)). The problem class is a convex, differentiable `f` on a Hilbert space with a minimizer and `‖x₀ − x⋆‖ ≤ R`. The oracle returns `(g(x,ξ), g(y,ξ))` from one fresh IID sample and satisfies three conditions: it is unbiased, it meets strong growth `E‖g − ∇f‖² ≤ Γ²‖∇f‖²`, and it is mean-squared smooth (MSS), `E‖g(x,ξ) − g(y,ξ)‖² ≤ L̄²‖x − y‖²`. The updates use `L̄`, `Γ`, `R`, `ε` and `x₀`.

**Complexity.** The budget is `⌈√(2L̄R²/((1+Γ)ε))⌉·⌈(1+Γ)²(4810 + 3200 log(1+Γ))⌉` pair calls. It counts every inner STORM call, the batch of `⌈6(1+Γ)²⌉` calls, and the warm-up. In order notation:

> **N = O( (1+Γ)^{3/2}(1+log(1+Γ))·√(L̄R²/ε) + (1+Γ)²(1+log(1+Γ)) )**

Here `L̄` is the MSS constant, `Γ` the relative noise level, `R` the initial distance and `ε` the expected accuracy. Below, `L ≤ L̄` is the true smoothness of `f`, which follows from MSS by Jensen. `L` is not a setup parameter.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vaswani–Bach–Schmidt, AISTATS 2019 ([arXiv 1810.07288](https://arxiv.org/abs/1810.07288)), Thm 2: stochastic AGD under SGC with `ρ = 1+Γ²` | `O((1+Γ²)√(LR²/ε))`, or `(1+Γ²)√(L̄R²/ε)` if tuned with the only public constant `L̄` → `N` | Factor ≈ `√(ΓL/L̄)/log(e(1+Γ))`. The gain needs `L̄ ≪ ΓL/(1+log(1+Γ))²` and `ε ≪ LR²/(1+log(1+Γ))²`. Against the `L̄`-tuned bound, the factor is ≈ `√Γ/log Γ` whenever `ε ≲ L̄R²/Γ`. Worse when `L̄ ≳ ΓL`. | None: the target class is the SGC class plus MSS, so it is narrower | None: both give a last-iterate bound in expectation with known constants | Needs MSS and a same-sample pair oracle. Adds an `ε`-independent `(1+Γ)² log` term and a `log(1+Γ)` factor. Large constants. |
| Gupta–Siegel–Wojtowytsch, NeurIPS 2024 ([arXiv 2302.05515 v3](https://arxiv.org/abs/2302.05515)), Thm 3 (AGNES, multiplicative noise `σ = Γ`) | `8L(1+Γ²)(1+2Γ²)R²/n²` ⇒ `O((1+Γ²)√(LR²/ε))` → `N` | Same as the row above | None | None | Same as the row above |
| Jain et al., COLT 2018 ([arXiv 1704.08227](https://arxiv.org/abs/1704.08227)), Thm 1. *Special case only:* realizable, strongly convex least squares | `O(√(κκ̃)·log(κκ̃dΔ/ε))` → `N` | Worse in `ε` on that overlap: the baseline has a linear rate, while `N` grows like `ε^{-1/2}` | Strongly convex quadratics → convex, non-quadratic, non-PL `f` | None | None beyond the first row |

**Reduction check.** Minibatching Vaswani's method costs `(b+Γ²)√(L/ε)`, so it gains nothing. A generic Catalyst/A-HPE outer loop with an inner SGD leaves noise relative to `‖∇f‖`, not `‖∇φ‖`, so it does not reproduce `N` either. The key step anchors MSS at the exact prox point, which makes the inner noise affine in `∇φ`. A STORM Lyapunov argument with a random window index then controls the inner solve. I found no prior derivation of this step.

**Proof ancestry, not competitors.** These sources supply the outer inequality, the inner estimator and the analogous rate shape. They do not supply the SGC + MSS noise control.

- Monteiro–Svaiter's A-HPE (SIAM J. Optim. 2013) supplies the outer inequality.
- STORM supplies the inner estimator.
- Allen-Zhu's Katyusha X ([arXiv 1802.03866](https://arxiv.org/abs/1802.03866), Thm 1) gives the finite-sum analogue `n + n^{3/4}√(L/σ)`, with `n ↔ Γ²`. It needs full gradients, so it does not apply here.
- Valls et al. ([arXiv 2207.11833](https://arxiv.org/abs/2207.11833), Thm 1) assume an estimator certificate in which the variance is bounded by gradient differences. It gives no end-to-end SGC sample cost.

**Further checks.**

- Mishkin–Pilanci–Schmidt ([arXiv 2404.02378 v2](https://arxiv.org/abs/2404.02378), Jan 2025) withdrew their `√ρ` claim. Their abstract and App. D say it is unknown whether `ρ` is tight.
- Dvinskikh et al. ([arXiv 2609.06555](https://arxiv.org/abs/2609.06555), Sept 2026), Thm 7 / Open Problem 2, give only unaccelerated strong-growth bounds.
- In the repository, [GapSmoothStrongGrowth](../../LongTails/Theorems/GapSmoothStrongGrowthHighProbability.lean) matches the `ρ√(LR²/ε)` order with high probability.
- **Instance check.** The companion note's smoothed-ℓ₄ Gaussian instance gives `L̄ ≲ √(trΣ·λ_max)`, `L = λ_max` and `Γ² ≈ trΣ/λ_min`. This yields a `κ_Σ^{1/4}` gain over accelerated SGD on a non-PL problem. I checked the MSS bound; the SGC constant is from the note and looks plausible.
- **Unverified note claims.** The note's zero-respecting lower bound and its SGD-on-instance comparison are not formalized, and I did not verify them. No optimality claim is made here.

**Search coverage.** On 2026-10-18 I searched arXiv, PMLR/NeurIPS sources and the web for strong growth, interpolation, MSS, STORM/SPIDER and acceleration under SGC, and read the cited theorems. Searches for online variance-reduced acceleration under SGC found nothing; that is not proof of priority. The result was introduced locally on 2026-10-18 (commit `8102682`). The note's citations to Vaswani et al., AGNES and Mishkin et al. check out. I did not re-read the Katyusha X theorem or the restarted-baseline rates.

**Conclusion**

**Yes: in a stated regime, the proved total complexity beats every accelerated strong-growth method I found.** The strongest baseline is stochastic Nesterov acceleration under strong growth (Vaswani et al. 2019, Thm 2; matched by AGNES).

| | Pair/sample calls for `E f − f⋆ ≤ ε` |
|---|---|
| Accelerated SGD under SGC | `(1+Γ²)√(LR²/ε)` |
| This result (SGC + MSS) | `(1+Γ)^{3/2} log(e(1+Γ))√(L̄R²/ε) + (1+Γ)² log(e(1+Γ))` |

The speedup is about `√(ΓL/L̄)/log(e(1+Γ))`. It survives when `L̄ ≪ ΓL/log²(e(1+Γ))` and `ε ≪ LR²/log²(e(1+Γ))`. A noisy regression instance with flat loss and an ill-conditioned covariance meets these conditions without being strongly convex. When `L̄ ≈ ΓL`, for example with coordinate-masking noise, the result loses by a logarithm and an additive term. On strongly convex least squares, a linear-rate method is better.

The price is a stronger model: mean-squared smoothness and a same-sample two-point oracle, which plain SGC methods do not need. The comparison proves an upper-bound gain over the known guarantees, not a lower bound on those methods. The literature search found no prior accelerated method that exploits MSS under strong growth, but that does not settle priority. The claimable contribution is a new accelerated complexity for the SGC+MSS oracle model, improving the growth-constant dependence from `Γ²√L` to `Γ^{3/2}√L̄` up to `log Γ`.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
