# Novelty assessment: TwoPhaseGaussianVI

[`TwoPhaseGaussianVI.lean`](../../LongTails/Theorems/TwoPhaseGaussianVI.lean) proves an expected-gap guarantee for full-rank Gaussian VI, F(m,C)=E V(m+Cξ)−Σ log Cᵢᵢ, over Cholesky C ([setup](../../LongTails/Setups/GaussianVariationalInference.lean)). Assume V is μ-strongly convex and L-smooth, with exact ∇V queries, and let R bound the initial distance to a Cholesky minimizer. The algorithm runs T constant proximal reparameterized SGD steps, followed by K decreasing steps with weighted averaging ([algorithm](../../LongTails/Algorithms/TwoPhaseGaussianVI.lean)). The public budget is the minimum of this two-phase count and the previous repository budget [`ReparameterizedGaussianVI`](../../LongTails/Theorems/ReparameterizedGaussianVI.lean). The output satisfies E[F(m̂,Ĉ)]−F⋆ ≤ ε.

**Proved complexity.** Here d is the dimension, κ=L/μ, and x=μR²/ε. The budget simplifies, with all terms kept, to

$$O\Big(1+(d+\log(48\kappa))\,\kappa\,\Big[\min\{1+\log\max(1,x),\ \sqrt{x}\}+\tfrac{d}{\varepsilon}\Big]\Big).$$

The previous repository theorem has √x in place of the minimum.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [`ReparameterizedGaussianVI`](../../LongTails/Theorems/ReparameterizedGaussianVI.lean) (commit f11d7961, 2026-11-09). Identical setup, oracle, and output. | O(1+(d+log κ)κ(√x+d/ε)) → O(1+(d+log κ)κ(min{1+log⁺x,√x}+d/ε)) | Startup √(μR²/ε) → log(μR²/ε). The gain is polynomial only when √(μR²/ε) ≫ d/ε+log x, i.e. μR²ε ≫ d². Example: d, κ, ε fixed and R→∞ gives a factor Θ(√x/log x). When μR²ε ≲ d², the gain is at most a constant factor. | None | None. Both give a weighted-average expected KL gap with the same known parameters. | The two-phase count adds about 4d/ε+32u, where u=(2+τ)κ and τ=3d+8 log(48κ). The `min` removes this loss. |
| Standard reduction (unformalized): Ghadimi–Lan multistage restart ([SIOPT 2013, Part II](https://doi.org/10.1137/110848876)), applied to the block estimate of the row-1 proof | O(u(1+log⁺x)+ud/ε) → same | None: same order. The constants improve: 8u·ln x replaces 52u·log₂x, and 32ud/ε replaces 256ud/ε. | None | Single switch instead of J restarts | None |
| Kim–Oh–Wu–Ma–Gardner, [NeurIPS 2023](https://arxiv.org/abs/2305.15349), Thm 7: fixed-step proximal SGD with the same estimator. Its criterion is last-iterate squared distance; this result implies distance with δ=2ε/μ. | O(dκ²(1+μ(‖z̄−m⋆‖²+tr Σ⋆)/ε)·log(μR²/ε)), worst case ≍ d²κ²/ε·log x → this result's bound above | The worst-case statistical term improves by a factor of about κ·log x·d/(d+log κ). This gain was already in row 1. The new part is only that the log startup is now combined with linear κ. | None (same class) | Last-iterate distance → averaged KL. KL implies distance; the converse is unchecked. | Averaged rather than last iterate |
| Park–Jang–Chen, [arXiv 2610.21020](https://arxiv.org/abs/2610.21020) (v1, Oct 2026, prior, unreviewed), Thms 4.1–4.2. Applies only to targets with an L_H-Lipschitz Hessian. | O((d√κ+λ_H²d³/ε)·log(Δ₀/ε)), λ_H=L_H/μ^{3/2} → this bound | Worse when λ_H²d ≲ κ (e.g. Gaussian targets, λ_H=0). Better when λ_H²d ≫ κ, up to logs. | Hessian-Lipschitz → C^{1,1} only | None | Unaccelerated |

**Reduction and mechanism.** The existing proof already bounds a block of k calls from any Cholesky start by 332μu²r/k²+16ud/k ([`GaussianVariationalGuarantee.lean`:106](../../LongTails/Proofs/GaussianVariationalGuarantee.lean)). Combined with μr/2 ≤ F−F⋆, halving restarts with k_j=⌈max(52u,128ud/s_j)⌉ give the same order as this theorem; I checked the arithmetic. The constant-then-decreasing schedule with suffix averaging is Stich's ([arXiv 1907.04232](https://arxiv.org/abs/1907.04232), Lemma 3/Thm 5). Kim et al. 2026 ([ICML 2026](https://arxiv.org/abs/2602.18718), Prop. 2.9) use the same schedule for proximal BBVI. These are proof ancestry: the new work is re-running the repository's existing κ-linear potential through a known switch. No new obstacle is overcome.

**Search coverage (2026-11-26).** I searched arXiv and the web for full-rank BBVI and Gaussian-VI complexity, switching schedules, and 2026 BW/natural-gradient work. I found no later gradient-only κ-linear result. The theorem statements of Kim'23 Thm 7 and Park'26 were taken from the earlier repository review and the companion note; I did not re-read them in this session. The companion note matches the Lean statement and itself concedes the restart reduction. I ran no build or audit.

## Conclusion

**No: this improves the repository's own earlier bound only by a standard restart/switching corollary, with no new rate for the problem class.** The baseline is the earlier repository theorem `ReparameterizedGaussianVI`, the only known κ-linear gradient-only bound for this setup.

| | startup | statistical |
|---|---|---|
| ReparameterizedGaussianVI | (d+log κ)κ√(μR²/ε) | (d+log κ)dκ/ε |
| this result | (d+log κ)κ·log(μR²/ε) | same |

The total gain is polynomial only in the low-accuracy, far-start regime μR²ε ≫ d². Otherwise the shared d/ε term dominates and the two bounds agree up to constants. The same order follows from Ghadimi–Lan halving restarts applied to the existing block estimate, or from Stich's constant-then-decreasing schedule. Both mechanisms are known, and the second has already been used for proximal BBVI.

What can be claimed is a formal single-switch certificate with smaller constants than the restart argument. The substantive κ-linear analysis belongs to the earlier theorem.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
