# Novelty assessment: GeneralizedSelfNormalizedConvex

The [theorem](../../LongTails/Theorems/GeneralizedSelfNormalizedConvex.lean) concerns convex f on a real Hilbert space with a differentiable gradient satisfying ‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖ ([setup](../../LongTails/Setups/GeneralizedSmoothAndConvex.lean)). For such f, the damped guess-and-check accelerated [algorithm](../../LongTails/Algorithms/DampedGeneralizedAccelerated.lean) uses exact gradients only, two per iteration, and returns a last iterate with f(x_K) − f(x\*) ≤ ε for every seed.

**Proved complexity.** The budget is 2⌈4096(1 + √(L₀R²/ε) + min{⌈(L₁R)^{2/3}⌉·ℓ, ℓ + (L₁R·ℓ)^{2/3}})⌉, with ℓ = log(4+4Δ/ε). It is 0 when Δ ≤ ε. Since ℓ ≥ log 4, the second branch of the min is never more than about twice the first, so the budget is

  **N = O(1 + √(L₀R²/ε) + log(1+Δ/ε) + (L₁R·log(1+Δ/ε))^{2/3})** gradient calls.

Here L₀ > 0 and L₁ ≥ 0 are the smoothness constants. R ≥ ‖x₀−x\*‖ and Δ ≥ f(x₀)−f\* hold for the same minimizer. The updates need L₀, L₁, R and Δ (the initial weight is R²/(2Δ)), and the stopping rule also needs ε. When L₁ = 0, the budget keeps its log term.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2508.06884](https://arxiv.org/abs/2508.06884) v2 (2026-05-21), Thm 4.3 with Thm 4.1, Alg. 2. Prior; gradient-only, one gradient per iteration. | O(1 + √(L₀R²/ε) + L₁R·log(1+min{L₁²Δ/L₀, Δ/ε}) + log(1+Δ/(L₀R²))) → O(1 + √(L₀R²/ε) + log(1+Δ/ε) + (L₁R·log(1+Δ/ε))^{2/3}) | Never worse up to constants (checked case by case below). Strictly better when L₁R·log(min{L₁²Δ/L₀, Δ/ε}) ≫ √(L₀R²/ε) + (L₁R·log(Δ/ε))^{2/3}. Example: q = L₁R → ∞, Δ = L₀R², ε = L₀R²q^{−4/3} gives Θ(q log q) → Θ((q log q)^{2/3}). | None: same class on ℝ^d (Hilbert-space scope is a routine dimension-free extension). | None: same parameters, last iterate. | 2 gradients per iteration instead of 1. Tyurin also covers general ℓ-smoothness. |
| Vankov–Rodomanov–Nedić–Sankar–Stich, [arXiv:2410.10800](https://arxiv.org/abs/2410.10800) v3, ICLR 2025, Thm 6.2 (AGMsDR) | (ν+1)·O(√(L₀R²/ε) + (L₁R)^{2/3}·log(2Δ/ε)) → O(1 + √(L₀R²/ε) + log(1+Δ/ε) + (L₁R·log(1+Δ/ε))^{2/3}) | In iterations: log^{1/3}(Δ/ε) fewer when (L₁R)^{2/3}log(Δ/ε) dominates and L₁R ≥ log^{1/2}(Δ/ε). Otherwise same order. As a call count, not comparable: ν is unbounded in these parameters. | None | None: both are last-iterate. Here updates also need R and Δ. | AGMsDR needs an exact minimization over a segment at every iteration (ν calls, including function values). The present method needs no line search. |
| Repository [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean) (9600c80, 2026-09-25) | O(1 + √(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉·log(1+Δ/ε)) → as above | Same log^{1/3} gain and regime as the Vankov row | None | None | Same algorithm. Only the analysis is new. |

**Case check against Tyurin.** If L₁R < 1, our extra terms are O(log(Δ/ε)). This is at most log(Δ/(L₀R²)) + O(√(L₀R²/ε)). If L₁R ≥ 1, split log(Δ/ε) = log(L₁²Δ/L₀) + log(L₀/(L₁²ε)). Tyurin's L₁R·log term absorbs the first part. For the second part, (L₁R·b)^{2/3} ≤ C·L₁R·e^{b/2} = C·√(L₀R²/ε).

**Admissibility of Tyurin's parameters.** As stated, Tyurin's theorem requires Γ₀ ≥ 2(f(x₀)−f\*)/‖x₀−x\*‖². However, the proof uses only V₀ ≤ Γ₀R̄² (eq. 34) and the final display. Both hold with Γ₀ = 2Δ/R² and R̄ = R if R² replaces ‖x₀−x\*‖² in the final bound. I used these values. Comparisons are between proved upper bounds; no lower bound on either method is established.

**Reductions and proof ancestry.** Rescaling leaves L₁R, L₀R²/ε and Δ/ε unchanged, so it gives nothing new. Specializing the other checked methods also gives nothing better. Restarting or localizing produces L₁R-linear or e^{L₁R} terms: [Gorbunov et al., ICLR 2025](https://arxiv.org/abs/2409.14989) has an exp(L₁R) factor, and [ARC-SG](https://arxiv.org/abs/2609.06555) (Remark 8, σ = 0) gives Õ(1 + L₁R + √(1+L₁R)·√(L₀R²/ε)). The new mechanism is the self-normalized charging lemma (`high_count_self_normalized` in [GeneralizedLogCharging](../../LongTails/Proofs/GeneralizedLogCharging.lean), used by `run_count_self_normalized`). It splits steps into low- and high-curvature steps. The high-curvature steps are bounded by an energy bound of order (L₁R)², plus logarithmic weight growth, combined through Hölder's inequality. The guess-and-damping structure resembles the momentum damping of Carmon et al. (NeurIPS 2022, MS acceleration); I did not re-read that source. The only lower bound I have is Nesterov's Ω(√(L₀R²/ε)) on the L₁ = 0 subclass. No lower bound for the startup term is known to me.

**Search coverage.** On 2026-10-07 I searched arXiv and proceedings for (L₀,L₁)/generalized-smooth acceleration. I read the theorem statements and proofs of Tyurin, Vankov et al., [Lobanov 2608.04884](https://arxiv.org/abs/2608.04884) (Aug 2026), GRAAL ([2507.09823](https://arxiv.org/abs/2507.09823), ICLR 2026) and ARC-SG (2026-09-06).
- Lobanov: the (H₀,H₁) class with (H₀,H₁) ≈ (2L₀, 3L₁²) gives Õ(√(L₀R̃²/ε) + L₁R̃·log(Δ/ε)). This uses the level-set radius R̃ ≥ R, restarts and segment minimization.
- GRAAL, Cor. 3: its startup term is L₁³D³, which is worse.

Git dates the result to 00fea6a (2026-09-28), and all of these sources predate it. I did not verify the ICML 2026 status of Tyurin's paper. There is no companion note. A prior repository review said Tyurin's bound needs a tight radius; I find that only the theorem's statement, not its proof, needs it.

## Conclusion

**Yes. Among gradient-only methods, the proved worst-case bound is never worse than the best previous one and is polynomially better when the L₁ startup term dominates.**

| | gradient calls for f(x_K) − f\* ≤ ε |
|---|---|
| Tyurin 2025/26 (gradient-only) | √(L₀R²/ε) + L₁R·log(min{L₁²Δ/L₀, Δ/ε}) + log(Δ/(L₀R²)) |
| This result | √(L₀R²/ε) + log(Δ/ε) + (L₁R·log(Δ/ε))^{2/3} |

With L₁R = q, Δ = L₀R² and ε = L₀R²/q^{4/3}, the bound drops from q log q to (q log q)^{2/3}. When √(L₀R²/ε) dominates, the two bounds are the same order.

Vankov et al.'s AGMsDR already has a (L₁R)^{2/3}·log(Δ/ε) startup. It needs an exact segment minimization at each iteration, with an unbounded call cost. Against its iteration count, the gain here is only log^{1/3}(Δ/ε), plus removing the line search. The repository predecessor already had both of those except the log^{1/3} improvement. So within this repository the theorem is incremental.

This is a comparison of upper bounds, not a lower-bound separation, and the optimal startup term is unknown. My search found no earlier line-search-free method with this startup; that supports priority but does not prove it.

The claimable contribution is a gradient-only accelerated method for convex (L₀,L₁)-smooth problems with startup (L₁R·log(Δ/ε))^{2/3}. It improves on Tyurin's L₁R·log startup and slightly sharpens Vankov's, without a line search.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
