# Novelty assessment: StrongGrowthMeanSquaredLowerBound

The [theorem](../../LongTails/Theorems/StrongGrowthMeanSquaredLowerBound.lean) proves a lower bound for a class of problems. Every randomized, adaptive algorithm that runs on the [setup](../../LongTails/Setups/EuclideanStrongGrowthMeanSquared.lean) with any budget `b ≤ B` (including 0) fails on some admissible instance, meaning its expected gap is `∫ f(x̂) − f(x⋆) > ε`. The setup is convex, differentiable `f` on `ℝ^d` with `‖x₀ − x⋆‖ ≤ R`, and an IID same-sample pair oracle `(g(x,ξ), g(y,ξ))` that is unbiased, satisfies strong growth with constant Γ², and is mean-squared smooth with constant L̄. The hard instance depends on the algorithm but not on its seed. The construction is in the [proof module](../../LongTails/Proofs/StrongGrowthMeanSquaredLowerBound.lean). This is a lower bound, so no algorithm is constructed.

**Proved necessary budget** (pair-oracle calls):

  B = Ω((1+Γ²)^{3/4} √(L̄R²/ε)) ≍ (1+Γ)^{3/2} √(L̄R²/ε).

The parameters are: L̄, the mean-squared smoothness constant; Γ², the strong-growth variance factor; R, the distance from x₀ to x⋆; ε, the target expected gap; and d, the dimension. The bound holds on this domain:
- `2^26 √(1+Γ²) ε ≤ L̄R²`;
- `d ≥ (L̄R²/(√(1+Γ²) ε))³`;
- R > 0, and the sample space has two measurable atoms.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Deterministic smooth convex lower bound (Nemirovski–Yudin 1983; Nesterov 2004, Thm 2.1.7; randomized version: Woodworth–Srebro, NeurIPS 2016). Applies because MSS implies `f` is L̄-smooth and an exact oracle is admissible. | Ω(√(L̄R²/ε)) → Ω((1+Γ²)^{3/4}√(L̄R²/ε)) | Larger by a factor of (1+Γ²)^{3/4}; this matters when Γ ≫ 1. Same order at Γ = O(1). | None | None | Needs polynomial dimension and the accuracy regime above. |
| Novoselov–Dorn–Dvinskikh–Gasnikov, [arXiv:2610.38354](https://arxiv.org/abs/2610.38354) v1 (28 Oct 2026, unrefereed), Thm A.10 with m = 1. This is a prior special-case baseline: single-point fresh queries, masked quadratics, individual smoothness H_s = ρL. | Inverting A.10 gives Ω(ρ√(LR²/ε)), where ρ = 1+Γ². Their masked oracle has same-sample MSS constant L̄ = √ρ·L. Substituting L = L̄/√ρ gives Ω(ρ^{3/4}√(L̄R²/ε)) → the same. | None: same order once the pair query is simulated by two exact gradients per informative call. | Single-point oracle → same-sample pair oracle with MSS (the classes are incomparable; the overlap is reached by masking). | None | A.10 states neither the MSS nor the pair-query version; that adaptation is the only added step. Their dimension requirement (d ≳ T²) is lighter than the cubic one here. |
| Repository upper bound [ProximalStormStrongGrowth](../../LongTails/Theorems/ProximalStormStrongGrowth.lean) (internal, 18 Oct 2026, unpublished), the same class through the [inclusion](../../LongTails/Proofs/StrongGrowthMeanSquaredInclusion.lean) | Upper bound O((1+Γ)^{3/2}√(L̄R²/ε)·log(e(1+Γ))) vs. this lower bound | Gap closed up to log(e(1+Γ)) on the valid regime | None | None | Tightness holds only where the accuracy term dominates. No matching lower bound is given for the `(1+Γ)² log` term. |

**Standard-reduction check.** The proof composes three things:
1. Bernoulli masking `g = ρ·1{ξ=a}∇f`. This is the "naive construction" of [Arjevani et al., arXiv:1912.02365, §3](https://arxiv.org/abs/1912.02365), Math. Program. 2023.
2. A coin-fixing simulation, which turns each informative pair call into two exact gradients.
3. The repository's randomized chain/hiding lower bound, run with smoothness L′ = L̄/√ρ.

Optimizing L′ is the only new calibration, and the companion note says so itself. I found no new technical mechanism.

**Search coverage.** I searched on 17 Nov 2026 (UTC) across arXiv, the Arjevani et al. paper, strong-growth acceleration (Vaswani et al. 2019; [Mishkin–Pilanci–Schmidt, arXiv:2404.02378 v2](https://arxiv.org/abs/2404.02378)), and the two Novoselov et al. preprints. I read A.10 and its proof directly. I did not read A.4–A.5 of 2610.38354 or G.1 of [2610.12641](https://arxiv.org/abs/2610.12641) verbatim. The note's citations check out with two discrepancies:
- Mishkin et al. v2 has no "Appendix D". The open question about whether the ρ dependence is tight appears in its abstract and §9.
- A.10 does not state the Ω(ρ√(LR²/ε)) corollary. It is a direct inversion of the theorem.

I found no published lower bound for exactly the SGC + MSS pair-oracle class.

## Conclusion

**This is a correct, explicitly stated lower bound, but it follows from a known construction by a one-parameter substitution.**

Compared with the trivial deterministic bound √(L̄R²/ε), the result raises the necessary call count by (1+Γ²)^{3/4}. That figure is exactly what masking gives: take the hard instance with smoothness L′ = L̄/√ρ, where each exact gradient costs about ρ calls:

  ρ · √(L′R²/ε) = ρ^{3/4} √(L̄R²/ε).

Arjevani et al.'s masking oracle (2019), combined with any randomized smooth-convex lower bound, already yields this. Novoselov et al.'s Theorem A.10 (Oct 2026, three weeks earlier) gives the single-query version Ω(ρ√(LR²/ε)) on the same masked instances. That version transfers to pair queries at constant cost.

The more interesting statement is the paired characterization Θ̃((1+Γ)^{3/2}√(L̄R²/ε)). It shows that same-sample, mean-squared-smooth access can beat the single-sample ρ√L rate when L̄ ≪ ΓL. However, the matching upper bound comes from the repository's unpublished ProximalStorm theorem, so it is a separate claim and not established by this lower bound. Tightness also holds only when ε ≤ L̄R²/(2^26√(1+Γ²)), with cubic dimension and up to log(e(1+Γ)).

What can be claimed is that the lower bound for this oracle class appears not to have been stated in print. It is a routine corollary of existing masking arguments, and its main value is certifying the ProximalStorm rate.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**
