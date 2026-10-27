# Novelty assessment: FiniteVarianceGeneralizedRadiusAcceleratedConvex

The [theorem](../../LongTails/Theorems/FiniteVarianceGeneralizedRadiusAcceleratedConvex.lean) proves the following for convex objectives on a separable Hilbert space with differentiable gradient, satisfying `‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖`, with a minimizer at distance at most R from x₀, and with IID unbiased stochastic gradients of variance at most σ² ([setup](../../LongTails/Setups/FiniteVarianceGeneralizedSmoothAndConvex.lean)). The [coarse warm start + restarted robust acceleration](../../LongTails/Algorithms/CoarseGeneralizedAccelerated.lean) returns its last accelerated iterate x̂ with `P{f(x̂) − f* > ε} ≤ δ`, using exactly the public budget. The algorithm never reads the supplied gap bound Δ: it replaces Δ with an internal certificate `restartGap`.

**Complexity.** Here L₀ and L₁ are the generalized-smoothness constants, R is the initial distance, σ² is the variance, ε is the accuracy and δ is the failure probability:

  N = O( (1 + L₁R + √(L₀R²/ε) + σ²R²/ε²) · log³( (2 + L₀R²/ε + L₁R + σR/ε)/δ ) ).

There is no dependence on Δ. Below, Õ hides polylogarithmic factors in K/δ.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| El Bakkali El Kadi–Gorbunov, [arXiv:2610.23301v2](https://arxiv.org/html/2610.23301v2), Thm 2 + Remarks 1–2, α=2 (preprint, v1 Oct 16 2026). This is a direct competitor. | Õ((1+L₁R)·log(2+Δ/(L₀R²)) + √(L₀R²/ε) + σ²R²/ε²); radius-only via Remark 2: Õ((1+L₁R)² + √(L₀R²/ε) + σ²R²/ε²) → N | Curvature term (L₁R)·log(Δ/(L₀R²)) → L₁R. Radius-only: (L₁R)² → L₁R, a factor-L₁R gain when (L₁R)² ≥ √(L₀R²/ε) + σ²R²/ε² | None. Their class is broader: it allows heavy tails with α<2 | Δ in the warm-up schedule → not needed. Both output the last iterate with high probability | Fixed factor log³ instead of their lower polylog powers. Constant 2⁷⁰. Only α=2 is covered |
| Repo [FiniteVarianceGeneralizedAcceleratedConvex](../../LongTails/Theorems/FiniteVarianceGeneralizedAcceleratedConvex.lean) (Oct 14 2026, unpublished; same setup) | O((1+√(L₀R²/ε)+Λ+(L₁RΛ)^{2/3})·log(e(1+L₀R²/ε+L₁R+Λ)/δ) + (σ²R²/ε²)·log²(e/δ)·log(e(1+L₀R²/ε+L₁R+Λ)/δ)), where Λ = log(4+4Δ/ε) → N | (L₁R·log(Δ/ε))^{2/3} → L₁R. This is better only when log(4+4Δ/ε) ≫ (L₁R)^{1/2}·polylog. Worst radius-only case Λ≈L₁R: (L₁R)^{4/3} → L₁R | None (same class) | Δ in the updates → not used | Worse when Δ ≤ poly(·): (L₁R)^{2/3}Λ^{2/3} < L₁R. The √(L₀R²/ε) term picks up two extra logs, and the V term picks up extra log² of accuracy |
| Gaash–Levy–Carmon, [NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/ae6c3f14de6f59ff9a44425a792e5bd1-Abstract-Conference.html), Thm 1, clipped SGD. Special case: sub-Gaussian noise only | Õ(L₀R²/ε + σ²R²/ε² + (L₁R)²) → N | L₀R²/ε → √(L₀R²/ε) and (L₁R)² → L₁R. This holds on all of their class | Sub-Gaussian noise → finite variance | None (both are radius-only) | None found on the overlap beyond log factors |
| Rudomanov et al., [arXiv:2610.21461v1](https://arxiv.org/abs/2610.21461), Thm 3.7 (Oct 15 2026). Special case: σ=0, deterministic | O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R)), with a matching deterministic lower bound Θ̃(√(L₀R²/ε)+L₁R) → N at σ=0 | Worse at σ=0 by log³ factors | Exact gradients → finite-variance stochastic gradients | None | At σ=0 the selected bound is weaker by polylogs |

**Reduction check.** None of the obvious reductions gives N:
- Substituting the radius gap bound Δ ≤ (L₀/L₁²)(e^{L₁R}−1−L₁R) into the competitors leaves the (L₁R)² or (L₁R)^{4/3} terms shown above.
- Minibatching the deterministic Everest warm start to accuracy-dependent precision multiplies its cost by a σ²-dependent factor.

The new step is a stability proof: the support-surplus/energy/counting warm start from Everest (Lemmas 3.2–3.5) survives gradient errors at a coarse tolerance σ + L₀R that does not depend on ε. That warm start then hands a polynomial gap certificate to the existing repo solver. Proof ancestry is the Everest mechanism plus the repo's robust accelerated solver; the composition with that solver is standard. In the cosh example below, the exponential gap makes the repo bound grow like (L₁R)^{4/3} while N grows like L₁R.

**Example.** The 1-D function f(x) = (L₀/L₁²)(cosh(L₁x) − 1) satisfies f'' ≤ L₀ + L₁|f'| because cosh ≤ 1 + |sinh|. Starting at x₀ = R, its initial gap is (L₀/L₁²)(cosh(L₁R) − 1), which is exponential in L₁R. So this is an admissible instance where log(Δ/ε) ≈ L₁R.

**Search coverage (2026-10-26).** I searched arXiv (2025–Oct 2026), NeurIPS 2025, and ICLR/ICML 2025–26 on stochastic, accelerated, and (L₀,L₁)-smooth convex optimization, and read theorem statements for the four rows.
- Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415](https://arxiv.org/abs/2609.33415), uses a different (H₀,H₁) condition. I did not read the theorem.
- ARC-SG [arXiv:2609.06555](https://arxiv.org/abs/2609.06555) assumes sub-Gaussian noise, and I did not verify it. The companion note says its Phase I is quadratic in L₁R.
- I did not find the companion note's citations to be wrong. However, its "h^{1/3} ratio" claim is asymptotic. Because of the log³ and 2⁷⁰ overheads, the gain appears only for very large L₁R.

**Conclusion**

**Yes: when the initial gap is exponential in L₁R, the proved complexity is polynomially better, and the bound no longer needs the gap at all.** The strongest published competitor is the one-phase Clip-SSTM of El Bakkali El Kadi–Gorbunov. The strongest overall baseline is the repository's own earlier solver on the identical setup.

| | curvature term (all also pay √(L₀R²/ε) + σ²R²/ε², up to logs) |
|---|---|
| Clip-SSTM, radius-only | (L₁R)² |
| repo solver, Λ = log(4+4Δ/ε) | (L₁R·Λ)^{2/3}, which is ≈ (L₁R)^{4/3} when Λ ≈ L₁R |
| this result | L₁R |

The gain over the repo solver survives when log(Δ/ε) ≫ (L₁R)^{1/2}·polylog and (L₁R)^{4/3} dominates √(L₀R²/ε) + σ²R²/ε². The cosh example shows that such exponential-gap instances satisfy every assumption. The result loses when a small Δ is known, and it carries extra log² factors on the √(L₀R²/ε) and noise terms. Up to polylogs it matches the deterministic lower bound of Everest plus the classical σ²R²/ε² term. A lower bound on the L₁R term for randomized or stochastic methods was not checked.

The comparison establishes the gain. Priority is less certain: the field is moving fast, the decisive deterministic mechanism appeared only 11 days earlier, and the result itself appeared on 2026-10-26. What can be claimed is a stochastic finite-variance high-probability bound of order L₁R + √(L₀R²/ε) + σ²R²/ε² (up to logs) that needs no gap information; the checked literature contains no such bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
