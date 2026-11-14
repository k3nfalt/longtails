# Novelty assessment: StructuredGaussianVI

[`StructuredGaussianVI.lean`](../../LongTails/Theorems/StructuredGaussianVI.lean) proves the following. Take a target V that is differentiable, has an L-Lipschitz gradient, and is μ-strongly convex. Fix any lower-triangular sparsity pattern S whose rows have at most w entries, and suppose the family has a minimizer (m⋆,C⋆) of F(m,C)=E V(m+Cξ)−Σ log Cᵢᵢ. Then single-sample masked reparameterized proximal SGD, run with steps 2/(μ(k+a)), returns a weighted average λ̂ in the family with E F(λ̂) − min_{𝒢_S} F ≤ ε. Cost is counted in pointwise ∇V calls ([setup](../../LongTails/Setups/StructuredGaussianVariationalInference.lean), [algorithm](../../LongTails/Algorithms/StructuredReparameterizedSgd.lean)).

**Proved complexity.** Here d is the dimension, w is the maximum row-support size (w=1 is mean-field, w=d is full-rank), R² ≥ ‖m₀−m⋆‖²+‖C₀−C⋆‖²_F, and ε is the excess-KL accuracy. The formula requires 0<μ≤L and C₀ in the family:

$$K=O\Big(1+\big(w+\log(dL/\mu)\big)\Big(\tfrac{LR}{\sqrt{\mu\varepsilon}}+\tfrac{dL}{\mu\varepsilon}\Big)\Big).$$

**Units for comparison.** Prior bounds are stated for the last-iterate distance E‖λ_T−λ⋆‖² ≤ ε_d. Because F is μ-strongly convex on the family, KL accuracy ε implies distance accuracy ε_d=2ε/μ. Translated, this result needs O((w+log(dL/μ))(LR/(μ√ε_d) + dL/(μ²ε_d))) calls. The reverse conversion (distance to KL) is not available. Below, Σ⋆=C⋆C⋆ᵀ, z̄=argmin V, and tr Σ⋆ ≤ d/μ (also tr Σ⋆ ≥ d/L for mean-field, by the diagonal optimality condition).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kim–Ma–Campbell–Gardner, [NeurIPS 2025, arXiv 2505.21721](https://arxiv.org/abs/2505.21721), Thm 3.2 with Cor 3.3 and Prop 3.4 (Gaussian base). **Mean-field only (w=1).** | O((L²/μ²)·log d·[(‖m⋆−z̄‖²+tr Σ⋆)/ε_d + √(‖m⋆−z̄‖²+tr Σ⋆)·log(R²)/√ε_d]) → O((1+log(dL/μ))(LR/(μ√ε_d) + dL/(μ²ε_d))) | Statistical term: worst case d(L/μ)² log d/(μ ε_d) → d(L/μ) log(dL/μ)/(μ ε_d). Example: the Gaussian target V=(μ/2)‖x‖²+((L−μ)/2)(1ᵀx)²/d with L ≤ (d+1)μ has m⋆=z̄=0 and tr Σ⋆ ≥ d/(2μ). Even Kim's δ=0 refinement leaves 8(L/μ)²·d/(2μ ε_d). The gain is a factor ≈ (L/μ)/log(dL/μ) when L/μ ≫ log(dL/μ) and R ≤ d/(μ√ε_d). | C² required → C^{1,1} only | Last-iterate distance → weighted-average KL. KL implies distance; distance does not imply KL. | Worse by a factor up to log(dL/μ)/log d when tr Σ⋆ ≈ d/L. With Kim's near-constant-Hessian refinement (δ≈0, no log d) on targets with L/μ ≲ log d, Kim can win by a factor of up to 1+log(dL/μ). Student-t bases are not covered here. Startup is polynomial (R/√ε_d) rather than log(R²)/√ε_d. |
| Ko–Kim–Kim–Gardner, [ICML 2024, arXiv 2401.10989](https://arxiv.org/abs/2401.10989), Thm 3 (Cor 2 for bordered block-diagonal). Coupled V uses N=M=1, which gives effective dimension d⋆=d for every pattern. | O([d(L/μ)²(‖m⋆−z̄‖²+tr Σ⋆)/ε_d + d(L/μ)²]·log(R²/ε_d)) → O((w+log(dL/μ))(LR/(μ√ε_d) + dL/(μ²ε_d))) | Worst-case statistical term d²(L/μ)²/(μ ε_d)·log → (w+log(dL/μ))·dL/(μ²ε_d), a gain of about d(L/μ)/(w+log(dL/μ)) when the statistical term dominates. | None (the same class of patterns and targets) | Last-iterate distance → weighted-average KL | When V=Σℓ_n decomposes with small per-component κ_n (separable or hierarchical targets), Ko's d⋆=d_z+d_y version can be much smaller. In that regime the two bounds are not ordered. Ko also covers component subsampling. |
| Repository [ReparameterizedGaussianVI](../../LongTails/Theorems/ReparameterizedGaussianVI.lean) (commit f11d7961, 2026-11-09, unpublished). **Full-rank only (w=d).** | O((d+log(L/μ))(LR/√(με)+dL/(με))) → the same bound with log(dL/μ) | None: same order at w=d | Full-rank family → every sparse-Cholesky family | None | Repository overlap only; not prior literature. |

**Reduction and mechanism.** The result does not follow from the full-rank theorem, because the family minimizer and the output space differ. Rerunning the full-rank argument with masked gradients gives only the factor d+log(L/μ). For mean-field that yields d²(L/μ)/(μ ε_d), which is worse than Kim'25 whenever d ≳ L/μ. The new step is the row-wise split on max_i Σ_{j∈S_i} ξ_j². It combines the repository's Bregman-divergence (κ-free) expected-smoothness argument with a maximum-of-χ² order-statistic bound, in the spirit of Kim'25 Prop 3.4, and adds a family-restricted optimality identity. As proof ancestry, Gower et al. / Garrigos–Gower supply the SGD potential, and the κ-free idea itself comes from the repository's unpublished full-rank result. Kim'25 Prop 4.2 (the lower bound "using only spectral bounds") concerns ‖λ−λ′‖²-relative variance, so it does not conflict with this result.

**Search coverage (2026-11-13).** I read the theorem text of Kim'25 (arXiv HTML, Thm 3.2, Cor 3.3, Prop 3.4, §5) and Ko'24 (Thms 2–3, Cor 2). I checked Park–Jang–Chen ([2610.21020](https://arxiv.org/abs/2610.21020), full-covariance only, with an extra Hessian-Lipschitz assumption) and Kim et al. ICML'26 ([2602.18718](https://arxiv.org/abs/2602.18718), full-rank, Hessian-based Price gradients). The latter itself lists mean-field BBVI as O((log d)κ² tr(μΣ⋆)/ε). Web searches for 2026 work on mean-field, structured, or sparse-Cholesky BBVI found no κ-linear bound; OpenReview 2026 submissions were not checked. The result was introduced in commit 2210b777 on 2026-11-13, so all cited papers predate it.

The companion note matches the Lean statement, with two caveats. Its claim of "nothing added" relative to Kim'25 omits that Kim'25 needs C², which this result does not. Its tightness claim via Park's κ^{1−o(1)} lower bound is unverified here; the full-rank review flagged that it needs μR² = polylog κ. I did not run a build or the axiom audit.

## Conclusion

**Yes: for gradient-only mean-field and structured Gaussian BBVI, the worst-case condition-number dependence improves from κ² to κ (κ=L/μ).** The strongest baselines are Kim–Ma–Campbell–Gardner (NeurIPS 2025) for mean-field and Ko et al. (ICML 2024) for general patterns. Both carry κ², and Kim et al. explicitly left open whether κ² is improvable.

| distance units ε_d=2ε/μ | statistical term (worst case) |
|---|---|
| Kim'25, mean-field | d κ² log d / (μ ε_d) |
| Ko'24, pattern S, coupled V | d² κ² log(R²/ε_d) / (μ ε_d) |
| this result | (w+log dκ) d κ / (μ ε_d) |

The gain is about κ/log(dκ) over Kim'25 when μ tr Σ⋆ ≈ d, for example on a rank-one-coupled Gaussian target. It needs κ ≫ log(dκ) and a statistical term that dominates startup, R ≤ d/(μ√ε_d). The result loses up to a log(dκ) factor when tr Σ⋆ ≈ d/L or on near-constant-Hessian targets. It can lose much more to Ko's decomposition-aware bound on separable or hierarchical targets with small per-component conditioning. The output is a weighted average with a KL guarantee, not a last iterate.

The comparison establishes the gain. Priority rests on a search that found no earlier κ-linear structured or mean-field bound, and the key κ-free mechanism is shared with the repository's own full-rank result from four days earlier. What can be claimed: the first κ-linear gradient-query complexity for mean-field and sparse-Cholesky Gaussian BBVI under strong log-concavity and log-smoothness alone. The row-wise tail split keeps the dimension factor at w+log(dκ).

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
