# Novelty review: KappaFreeSgdPLHessian

[`result`](../../LongTails/Theorems/KappaFreeSgdPLHessian.lean) proves the following under the [setup](../../LongTails/Setups/PLHessianLipschitzKurtosis.lean). Take constant-step SGD whose output is a uniformly random iterate from a final window ([`WindowSgd`](../../LongTails/Algorithms/WindowSgd.lean); the setup's `allowedAlgorithm` enforces this, and compliance is proved). Run it on a finite-dimensional, globally PL function with an attained minimum, an L-Lipschitz gradient and a ρ-Lipschitz Hessian. The minimizer set may be non-isolated. The oracle draws i.i.d. samples and is unbiased, with variance at most σ² and fourth central moment at most Kσ⁴. Within the stated budget, SGD returns x̂ with `∫ f(x̂) − f(x⋆) dP ≤ ε`.

**Complexity.** Parameters: smoothness L, PL constant μ, Hessian-Lipschitz constant ρ, variance σ², kurtosis K ≥ 1, initial gap Δ ≥ f(x₀) − f⋆, target ε. The Lean budget simplifies to

  T = O( [ (L/μ)^{5/4} + K L^{3/2} σ² ρ² / μ^{11/2} + σ²/(με) ] · [ 1 + log(1 + √(L/μ) Δ/ε) ] ).

Write ℓ for the bracketed logarithm factor and κ = L/μ.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SGD under PL: Khaled–Richtárik, [arXiv 2002.03329](https://arxiv.org/abs/2002.03329) (TMLR 2023), Thm 3 / Cor. 2 with A=0, B=1, C=σ². Prior. Direct competitor on a broader class. | O(κ log(Δ/ε) + κσ²/(με)) → O((κ^{5/4} + Kκ^{3/2}σ²ρ²/μ⁴ + σ²/(με))·ℓ) | Leading term loses its κ factor: speedup ≈ κ/ℓ. This requires ℓ ≪ κ, ε ≪ σ²/(μ^{3/4}L^{1/4}ℓ) and ε ≪ μ^{7/2}/(K L^{1/2}ρ²ℓ). | None; the class is narrower. | Last iterate → random window iterate. | Adds a Lipschitz Hessian and a uniform kurtosis bound. Deterministic term κ log → κ^{5/4}ℓ. Adds an ε-independent ρ-term. The σ²/(με) term carries ℓ, so the bound is worse for ε ≲ √κ Δ e^{−κ}. |
| Lower bound: Masiha–Kiyavash–Thiran, [arXiv 2606.28278](https://arxiv.org/abs/2606.28278) v3 (Aug 2026), Thm 4.3 and Remark 4.6. Prior. | Ω(κσ²/(με)) for every first-order method on the C^{1,1} global-PL class → above | The κ factor cannot be removed on the C^{1,1} class. Hard instances are piecewise C¹, and the oracle has unbounded kurtosis. | Not applicable: the C^{1,1} class → the Hessian-Lipschitz, bounded-kurtosis subclass, which escapes the lower bound. | None | It is open whether either extra assumption alone suffices. |
| Strongly convex special case: Stich, [arXiv 1907.04232](https://arxiv.org/abs/1907.04232), Thm 5 (weighted average; R² ≤ 2Δ/μ). Prior. | O(κ log(κΔ/ε) + σ²/(με)) → above | Worse on this overlap: extra κ^{1/4}, the ρ-term, and the log on σ²/(με). | Strong convexity (unique minimizer) → PL with non-isolated minimizers. | Comparable (both use weighted or windowed outputs). | Needs ρ and K. |
| Isolated minimizer: Gadat–Panloup, [arXiv 1709.03342](https://arxiv.org/abs/1709.03342) (Stoch. Process. Appl.), Thm 2 (Ruppert–Polyak averaging). Prior. | Tr(Σ⋆)/n + C n^{−r} in squared distance, with C non-explicit → above | Not comparable: C is not explicit, and the criterion is distance. | Unique minimizer with ∇²f(x⋆) ≻ 0 → non-isolated minimizers with explicit constants. | Averaged iterate vs window sample. | Gadat–Panloup's own covariance and Lᵖ-consistency assumptions differ. |

**Reductions and proof ancestry.** The proof's local aiming step is Liu–Drusvyatskiy–Belkin–Davis–Ma ([arXiv 2306.02601](https://arxiv.org/abs/2306.02601), Thm 2.2). That paper's SGD rates are local and assume interpolation (σ=0). Near the minimizers, the distance-potential step is the standard SGD argument under strong aiming (Gower–Sebbouh–Loizou, AISTATS 2021). The ingredient I could not find published is the global gluing. It takes the potential dist² + λ·Huber(f − f⋆) and needs the kurtosis bound to control jumps into the far field. The naive two-phase reduction (reach the aiming region, then run local SGD) needs containment with σ>0, and I found no theorem that supplies it.

**Search coverage (2026-10-17).** I searched arXiv, NeurIPS/PMLR and journals for SGD under PL with a Lipschitz Hessian, manifolds of minimizers, and averaging. I read the cited theorems above. Kassing–Kruse ([arXiv 2605.14663](https://arxiv.org/abs/2605.14663), May 2026) is asymptotic, local, and assumes multiplicative noise that vanishes at the minimizers. SCRN (Masiha et al., NeurIPS 2022, Remark 5) uses a stochastic Hessian oracle and attains τ_F^{7/4}/ε (τ_F = 1/(2μ) is the PL constant), so it is not κ-free. Neither is a competitor. I did not read the full texts of Dereich–Kassing (asymptotic CLTs on stable manifolds) or Fehrman–Gess–Jentzen. The companion note's citations and regime statements match the Lean budget.

**Conclusion**

**Yes: when ε is small, this gives a provably better total complexity on a natural subclass of PL problems.** The strongest applicable baseline is SGD under PL (Khaled–Richtárik). Its κ factor in the leading term is unavoidable on the plain smooth PL class, so no first-order method can beat it there.

| | budget |
|---|---|
| before | κ log(Δ/ε) + κσ²/(με) |
| after | (κ^{5/4} + Kκ^{3/2}σ²ρ²/μ⁴ + σ²/(με))·ℓ |

The gain is about κ/ℓ. It requires ε ≪ min{σ²/(μ^{3/4}L^{1/4}), μ^{7/2}/(K L^{1/2}ρ²)}/ℓ, and it shrinks back to nothing once log(√κΔ/ε) exceeds κ. Example: take μ=σ=ρ=Δ=1, K=3, L=κ, ε=κ⁻². The cost then drops from about κ³ to κ² log κ. The price is the extra Hessian-Lipschitz and bounded-kurtosis assumptions, a worse κ^{5/4} deterministic term, and a loss to standard SGD bounds on strongly convex instances.

The comparison establishes the gain. The literature search separately supports priority: I found no earlier non-asymptotic κ-free bound for non-isolated minimizers with σ>0. That search cannot be exhaustive, and the asymptotic manifold papers were only partly read. What can be claimed is a removal of κ from SGD's statistical term under PL plus a Lipschitz Hessian and bounded kurtosis, a regime that escapes the 2026 lower bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
