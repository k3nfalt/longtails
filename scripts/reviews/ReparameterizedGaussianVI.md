# Novelty assessment: ReparameterizedGaussianVI

[`ReparameterizedGaussianVI.lean`](../../LongTails/Theorems/ReparameterizedGaussianVI.lean) proves the following. Take a target V that is differentiable, μ-strongly convex, and has an L-Lipschitz gradient, with a Cholesky minimizer (m⋆,C⋆) of the Gaussian-VI objective F(m,C)=E V(m+Cξ)−Σ log Cᵢᵢ. Then single-sample reparameterized proximal SGD, with steps 2/(μ(k+a)) and a weighted-average output, gives expected excess KL E F(λ̂)−F⋆ ≤ ε. The cost is counted in pointwise ∇V calls ([setup](../../LongTails/Setups/GaussianVariationalInference.lean), [algorithm](../../LongTails/Algorithms/ReparameterizedProxSgd.lean)).

**Proved complexity.** In this formula, d is the dimension, κ=L/μ, R² ≥ ‖m₀−m⋆‖²+‖C₀−C⋆‖²_F is the squared initial distance, and ε is the KL accuracy:

$$K=O\!\Big(1+\big(d+\log(L/\mu)\big)\Big(\tfrac{LR}{\sqrt{\mu\varepsilon}}+\tfrac{dL}{\mu\varepsilon}\Big)\Big).$$

**Comparison convention.** For prior results stated in distance, the KL guarantee implies E‖λ̂−λ⋆‖² ≤ ε_d := 2ε/μ. The reverse conversion (distance to KL) does not hold in general, because the entropy term is not smooth. Write Σ⋆=C⋆C⋆ᵀ and z̄=argmin V. The trace satisfies d/L ≤ tr Σ⋆ ≤ d/μ.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kim–Oh–Wu–Ma–Gardner, [NeurIPS 2023](https://arxiv.org/abs/2305.15349) (v4), Thm 7 (Thm 4 is the decaying-step analogue with R/√ε_d in place of the log); same order as Domke–Gower–Garrigos, [NeurIPS 2023](https://arxiv.org/abs/2306.03638), Thm 7 with a=2(d+3)L², step ≤ μ/(2a). Same algorithm family and oracle. | O(d[κ² + L²(‖z̄−m⋆‖²+tr Σ⋆)/(με)]·log(μR²/ε)), which lies between O(d²κ/ε·log) and ≳ d²κ²/ε·log → O((d+log κ)(κ√(μR²/ε)+dκ/ε)) | The worst-case statistical term drops from d²κ²/ε to (d+log κ)dκ/ε, a factor of about κd/(d+log κ). Example: V(x)=(L/2)x₁²+(μ/2)Σ_{i≥2}xᵢ²+(μ/2)log cosh x₂ with L ≥ 1.5μ. Here tr Σ⋆ ≥ (d−1)/(1.5μ) and z̄=m⋆=0. The gain survives whenever √(μR²/ε) ≲ d·κ/ε. | None (same class) | Last-iterate distance → weighted-average KL. KL implies distance; no converse is checked. | Ties up to a factor 1+log κ/d when tr Σ⋆ ≈ d/L. Polynomial √(μR²/ε) startup instead of log(μR²/ε), so it is worse when √(μR²/ε) ≫ κ log(μR²/ε) + d/ε. |
| Kim–Fu–Ma–Gardner–Campbell, [ICML 2026](https://arxiv.org/abs/2602.18718) (v2, May 2026), Thm 3.3, Price estimator | Not comparable. That result needs O(dκ/ε + √d κ^{3/2} log(κμR²)/√ε + κ² log(1/ε)) iterations for μE‖λ−λ⋆‖² ≤ ε, and each iteration needs Cᵀ∇²V(m+Cξ), i.e., a Hessian or d HVPs. | Not comparable: different oracle. In HVP units it costs about d²κ/ε, the same order as this result. | None | None | This result uses only gradients. Price is a factor d better in iteration count. |
| Park–Jang–Chen, [arXiv 2610.21020](https://arxiv.org/abs/2610.21020) (v1, 14 Oct 2026, unreviewed), Thms 4.1/4.2. Restricted to targets with an L_H-Lipschitz Hessian. | O((d√κ + λ_H²d³/ε) log(Δ₀/ε)) with λ_H=L_H/μ^{3/2} and Δ₀ the initial gap → O((d+log κ)(κ√(μR²/ε)+dκ/ε)) | On the overlap, this result is worse when λ_H²d ≲ κ (for Gaussian targets λ_H=0, so Park et al. win by a polynomial factor). It is better roughly when λ_H²d ≫ κ, up to logs and initialization terms. | Hessian-Lipschitz (C², L_H<∞) → only C^{1,1}, which also covers non-twice-differentiable V | None (both give expected KL) | Park et al. accelerate and need fewer gradient calls on smooth-Hessian targets. |

**Reduction and mechanism.** Batching, mini-batching, or restarting the Kim/DGG analysis cannot remove κ², because their expected-smoothness constant 2Lκ(d+3) forces about dκ² gradient calls regardless of batch size. The new ingredient is a κ-free expected-smoothness bound. In `expected_smoothness`, a χ²-tail split at ‖ξ‖² ≤ 3d+8log(48κ) gives the constant 2L(2+τ). It is paired with a first-order-optimality variance bound σ⋆² ≤ (2+τ)Ld (`variance_at_optimum`). The first-order optimality identity behind that bound parallels ICML'26 Lemma 3.4, which is stated for the Price estimator. That lemma still carries 10Lκ. The SGD engine (Gower et al. 2019 / Garrigos–Gower 2023) is proof ancestry only. Kim et al. NeurIPS 2025 (Lemma 4.1, Remark 4.3) say their variance bound cannot be improved "using only spectral bounds". That bound is stated relative to ‖λ−λ′‖², not to the Bregman divergence. So it does not contradict this result.

**Search coverage (2026-11-09).** I searched arXiv, the NeurIPS, ICML and ICLR proceedings, and web indexes for full-rank BBVI, Bures–Wasserstein, and natural-gradient Gaussian VI. I read the theorem text of Kim'23, DGG'23, Kim'26 and Park'26. Kim'25 and Luu et al. ([ICLR 2025](https://arxiv.org/abs/2410.02490)) I read only partially; Luu et al. use Hessians. I found no prior first-order bound linear in κ under these assumptions. OpenReview submissions for 2026 and some appendices were not checked. The result was introduced in commit f11d7961 on 2026-11-09, so Park'26 is prior work. The companion note matches the Lean statement. Two of its claims go beyond what was checked: the W₂ corollary is not formalized, and the claim that the bound matches Park's κ^{1−o(1)} lower bound "up to κ^{o(1)}" needs μR²=polylog κ on Park's hard family, which I did not check. I did not run a build or the audit.

## Conclusion

**Yes: for gradient-only Gaussian VI under just strong log-concavity and log-smoothness, the worst-case condition-number dependence improves from κ² to κ.** The strongest same-oracle baseline is Kim et al. (NeurIPS 2023), whose order is matched by Domke–Gower–Garrigos. The algorithm is their standard proximal SGD; what is new is the analysis.

| | statistical term | startup term |
|---|---|---|
| Kim et al. Thm 7 (worst case) | d²κ²/ε · log(μR²/ε) | dκ² log(μR²/ε) |
| this result | (d+log κ)·dκ/ε | (d+log κ)·κ√(μR²/ε) |

The gain, up to a factor κd/(d+log κ), is realized on non-Gaussian targets with many weakly curved directions. When tr Σ⋆ ≈ d/L the two results tie, and this result loses when √(μR²/ε) ≫ κ log + d/ε. The guarantee is also in expected KL rather than distance, but for a weighted average rather than the last iterate. Park et al. (Oct 2026) do better when the Hessian is Lipschitz and nearly constant; this result covers targets without Hessian regularity.

The comparison establishes the gain. Priority rests on a search that found no earlier linear-κ first-order bound, and very recent submissions may have been missed. What can be claimed: a new κ-free variance analysis of reparameterized proximal SGD, which gives the first verified κ-linear gradient-query complexity for this problem class.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
