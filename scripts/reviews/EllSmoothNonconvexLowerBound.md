# Novelty assessment: EllSmoothNonconvexLowerBound

[`result`](../../LongTails/Theorems/EllSmoothNonconvexLowerBound.lean) is a `NonConvergence` statement on [HighDimensionalEllSmoothNonconvex](../../LongTails/Setups/HighDimensionalEllSmoothNonconvex.lean) (which restricts [EllSmoothNonconvex](../../LongTails/Setups/EllSmoothNonconvex.lean)). It says the following. Fix any regular ℓ of order ρ < 2 with ℓ(0) > 0. Consider every randomized algorithm, with any seed law, that knows all parameters and makes adaptive, unbounded queries to an exact (f, ∇f) oracle, and every budget b ≤ ⌊(2−ρ)Δℓ(ε)/(2²⁷ε²)⌋. For each such pair there is an f : ℝᵈ → ℝ with ‖∇²f(x)‖ ≤ ℓ(‖∇f(x)‖) and f(x⁰) − inf f ≤ Δ on which E‖∇f(x̂)‖ > ε. There is no `allowedAlgorithm` restriction. The hard instance depends on the algorithm and on b, but not on the realized seed.

**Proved lower complexity.** Here ℓ is the curvature profile, nondecreasing with ℓ(u)/u^ρ nonincreasing; Δ is the initial gap; ε is the target E‖∇f‖; d is the dimension.

  Ω((2−ρ)·Δℓ(ε)/ε²), and for ℓ(u) = L₀ + L_ρu^ρ: Ω((2−ρ)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})).

The theorem requires ρ < 2, L₀ = ℓ(0) > 0, 2²⁷ε² ≤ (2−ρ)Δℓ(ε), and d ≥ 2⁵⁶(N+1)⁶(ℓ(ε)/ℓ(0))⁴, where N is the budget. `highDimensional_valid_nonempty` shows that this regime is nonempty. On the same base class, the companion [upper bound](../../LongTails/Theorems/EllSmoothNonconvexUpperBound.lean) (normalized-step GD, Tyurin's rate) uses ⌊16Δℓ(ε)/ε²⌋ + 1 calls. The remaining gap is therefore the factor 2³¹/(2−ρ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon–Duchi–Hinder–Sidford, [arXiv:1710.11606](https://arxiv.org/abs/1710.11606) (Math. Program. 2020), Thm. 2, randomized. *Special case:* L-smooth functions with L = ℓ(0), embedded into the class | Ω(L₀Δ/ε²) → Ω((2−ρ)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})) | Larger by a factor of order (2−ρ)(1 + L_ρε^ρ/L₀); polynomial when L_ρε^ρ ≫ L₀ | None: same instance class (the old hard functions are members) | None | Worse by the factor (2−ρ) when L_ρε^ρ ≲ L₀. Dimension is degree 6 in N rather than Carmon's milder requirement |
| Liang–Luo, [arXiv:2610.21692](https://arxiv.org/abs/2610.21692) (v1 15 Oct 2026, prior), Thm. 4.5 at σ = 0, randomized, E‖∇f‖ criterion. Applies to ρ ∈ (1,2) only through the Young embedding L₀′ + L₁′u ≤ L₀ + L_ρu^ρ | Ω(L₀Δ/ε² + ΔL_ρ^{1/ρ}L₀^{(ρ−1)/ρ}/ε) → Ω((2−ρ)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})) | ρ ∈ (1,2): larger by (L_ρε^ρ/L₀)^{(ρ−1)/ρ} when L_ρε^ρ ≥ L₀. ρ ≤ 1: none, same order | None. Their class is the local gradient-difference (L₀,L₁) condition, not the Hessian condition | None | Much larger dimension: theirs is ≈ T + R² log T with R ∝ √T/μ. Loses (2−ρ) |
| Shulgin–Sadiev, [OPT 2026 workshop](https://neurips.cc/virtual/2026/161557) (prior; only the abstract was checked). Deterministic methods, ρ = 1 Hessian class | Ω(L₀Δ/ε² + L₁Δ/ε) (ρ = 1 only) → same order at ρ = 1 | None at ρ = 1 | ρ = 1 → every ρ ∈ [0,2) and general regular ℓ | Deterministic → randomized algorithms | Stronger dimension requirement |

I verified the Young-embedding exponent myself: Lρ·Δ/ε^{2−ρ} divided by Δ·Lρ^{1/ρ}·L₀^{(ρ−1)/ρ}/ε equals (Lρε^ρ/L₀)^{(ρ−1)/ρ}. For example, ρ = 3/2 and L_ρε^ρ = L₀·10⁶ give a gain of 100. The reduction fails because ρ = 1 chains have curvature ≍ L₁′g at small g, which exceeds L_ρg^ρ.

**Reduction check and proof ancestry.** No embedding or rescaling of the ρ ∈ {0,1} instances gives the L_ρΔ/ε^{2−ρ} term for ρ > 1. The new mechanism has three parts. First, a terminated power-law tail whose exponent is tied to ρ, with uniformly bounded mass. Second, a proof that the chain, cut-off and wall preserve ‖∇²‖ ≲ ϑ⁻¹min(1, ‖∇‖^{2−ϑ}) + μ on all of ℝᵈ. Third, scaling by ℓ(ε). The two-sided zero-chain and the random-coordinate hiding come from Carmon et al. and the repository's `SmoothConvexFiniteHiding` counting lemma. Li et al. ([NeurIPS 2023](https://arxiv.org/abs/2306.01264), Thm. 5.4) give only a GD-specific statement, for ρ = 2. Tyurin ([ICML 2025](https://arxiv.org/abs/2412.11773)) states no class lower bound.

**Search coverage (2026-11-21).** I searched arXiv, NeurIPS/ICML proceedings and the web for lower bounds under ℓ-, (ρ,L₀,L_ρ)-, α-symmetric and (L₀,L₁)-smoothness, and found no lower bound for ρ ∈ (1,2). For Liang–Luo, I read the theorem statement in v2 (15 Nov 2026) only through a summary, and checked their class definition and criterion directly. For Shulgin–Sadiev only the abstract was available. The result entered the repository on 2026-11-21 (commit d4b14a20), after both papers. The companion note matches the Lean statement. It omits that Liang–Luo use the gradient-difference class rather than the Hessian class.

**Conclusion**

**Yes, for ρ ∈ (1,2): this is a new, nearly tight lower bound that standard reductions do not give.** The strongest relevant baseline is Liang–Luo's randomized (L₀,L₁) bound, transferred by the best class embedding:

  Ω(L₀Δ/ε² + ΔL_ρ^{1/ρ}L₀^{(ρ−1)/ρ}/ε)  →  Ω((2−ρ)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})).

When L_ρε^ρ ≫ L₀ (curvature driven by the gradient dominates), this is larger by the factor (L_ρε^ρ/L₀)^{(ρ−1)/ρ}. It matches Tyurin's GD upper bound up to 2³¹/(2−ρ).

At ρ ≤ 1 the theorem only re-proves known rates; it adds nothing at ρ = 1 and is a routine consequence for ρ < 1. It also requires L₀ > 0, ρ < 2, and a dimension of order N⁶(1 + L_ρε^ρ/L₀)⁴. The constant degrades as ρ → 2, and ρ = 2 remains open.

The comparison establishes a real gain over all checked bounds. My search found no earlier lower bound for ρ > 1, but that does not prove priority, and I did not read the full text of the two 2026 papers. The contribution that can be claimed is the first checked algorithm-independent lower bound showing that GD's Δℓ(ε)/ε² rate is optimal, up to a (2−ρ)-dependent constant, for every regular ℓ of order ρ < 2.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
