# Clipped projected subgradient for weakly convex heavy-tailed optimization

The [theorem](../../LongTails/Theorems/WeaklyConvexClippedSubgradient.lean) proves the following for the [single-loop projected clipped subgradient method](../../LongTails/Algorithms/ClippedProjectedSubgradient.lean) with constant step and threshold, run on the [setup](../../LongTails/Setups/WeaklyConvexHeavyTailed.lean): ρ-weakly convex f on a closed convex X ⊆ ℝᵈ, with the selected subgradients bounded by G, gap Δ, and unbiased noise with central α-moment at most σ^α, α ∈ (1,2]. The output is a uniformly random iterate x_J, and it satisfies E‖∇f_{1/(2ρ)}(x_J)‖² = E[(2ρ)²‖x_J − x̂_J‖²] ≤ ε².

**Selected complexity.** The budget is 2T, counting one subgradient call and one projection call per step:

  O( 1 + ρΔ(G² + σ^α G^{2−α})/ε⁴ + ρΔ σ^{α/(α−1)} ε^{−(3α−2)/(α−1)} ),

and it is 0 when Δ = 0. The cross term is never dominant once ε < 2G. If ε ≥ 2G, x₀ is already accurate, because ‖∇f_{1/(2ρ)}‖ ≤ 2G.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhu–Xu–Wang–Ji, ICML 2026, Thm E.1 eq. (84) (in expectation; [arXiv:2507.13283v1](https://arxiv.org/abs/2507.13283), Jul 2025, Thm 5). This is the same Clip-SGD with λ = 2G∨σT^{1/α}. | O((Δ+G+ρ)²G²/ε⁴ + ((Δ+G+ρ)σ/ε²)^{α/(α−1)}) → O(ρΔ(G²+σ^αG^{2−α})/ε⁴ + ρΔσ^{α/(α−1)}ε^{−(3α−2)/(α−1)}) | The ε-exponent drops from 2α/(α−1) to (3α−2)/(α−1) (6 → 5 at α = 1.5). The noise term is smaller iff ε^{(2−α)/(α−1)} < (Δ+G+ρ)^{α/(α−1)}/(ρΔ), which holds for all small ε when α < 2. There is no gain at α = 2. | None: same class | None: same random-iterate output. Both methods need σ, G, α; the new step also uses ρ, Δ, ε. | In expectation only. The baseline also has a high-probability version with log(1/δ) (Thm 5.1). The baseline's G-term (Δ+G+ρ)² is dimensionally inhomogeneous, so the two G²/ε⁴ terms are not comparable. |
| Verified reduction for X = ℝᵈ: inexact proximal point (outer loop of Davis–Grimmer, [SIOPT 2019](https://arxiv.org/abs/1707.03505)) + inner Liu–Zhou [arXiv:2303.12277v3](https://arxiv.org/abs/2303.12277) (May 2023, unpublished) Thm 9 | O(ρΔG²/ε⁴ + ρΔσ^{α/(α−1)}ε^{−(3α−2)/(α−1)}) → same order | None: same order, and no logarithm on either side | None | Same random-outer-iterate output. Double loop vs single loop; the inner solver uses G, σ, ρ. | The reduction needs projection onto B(x_k, G/ρ), which is closed-form for X = ℝᵈ |
| Same reduction for bounded X with diameter D, using only Π_X | O(ρΔ(G+ρD)²/ε⁴ + ρΔσ^{α/(α−1)}ε^{−(3α−2)/(α−1)}) → selected | Same leading noise term. The deterministic term improves by (1+ρD/G)² when ρD > G. | Bounded X → unbounded X with only Π_X (the reduction there is unresolved) | None | None found |

**Reduction check.** Write φ = f_{1/(2ρ)}. The bound φ(z) ≤ f(x̂_k) + ρ‖x̂_k − z‖² gives Eφ(x_{k+1}) ≤ Eφ(x_k) − E‖∇φ(x_k)‖²/(4ρ) + ρe when E‖x_{k+1} − x̂_k‖² ≤ e. So K = 8ρΔ/ε² outer steps with e = ε²/(8ρ²) suffice.

Each subproblem f + ρ‖·−x_k‖² is ρ-strongly convex. Its minimizer lies within G/ρ of x_k, and on that ball its subgradients are bounded by 3G. Liu–Zhou's Thm 9 gives the last-iterate bound E‖y_{T+1}−x̂_k‖² ≤ O(G²/(ρ²T) + σ²/(ρ²T^{2(α−1)/α})), so T_in = O(G²/ε² + (σ/ε)^{α/(α−1)}) inner steps suffice. Multiplying by K gives the second row.

For X = ℝᵈ, the selection hypothesis implies true weak convexity and G-Lipschitz continuity, so Thm 9 applies. For general constrained X, the obstacle is that only Π_X is supplied, not projection onto X ∩ ball. The new mechanism is absorbing the clipping bias quadratically into the Moreau descent term, as in Zhang et al. (NeurIPS 2020, Thm 2), instead of bounding it linearly by G/ρ as Zhu et al. do. This is what makes single-loop Clip-SGD reach the exponent.

**Search coverage.** I searched on 2026-10-09 across arXiv, the ICML 2026 paper (poster 64202, full text read), NeurIPS 2025 (Fatkhullin–Hübler–Lan: convex and smooth only), and 2025–2026 preprints on weakly convex and heavy-tailed problems. I found no paper that states this weakly convex bound. I did not check Hu et al. ([arXiv:2505.09279](https://arxiv.org/abs/2505.09279)) in detail, and I did not recheck the note's transfer of the Zhang et al. lower bound.

The [companion note](../../LongTails/Theorems/WeaklyConvexClippedSubgradient.md) is accurate about Zhu et al.'s rates and their open question. However, it omits the proximal-point reduction. Its claim that the result shows "nonsmoothness … cost nothing in the exponent" was already derivable from the 2019 and 2023 results for X = ℝᵈ. The result was introduced in commit `a519747` (2026-10-09). All the reduction ingredients predate it.

## Conclusion

**The rate is not new for the problem class: the gain is that single-loop Clip-SGD now attains it.** Compared with the only direct analysis of this method, Zhu–Xu–Wang–Ji (ICML 2026), the ε-exponent genuinely improves:

  ε^{−2α/(α−1)} → ε^{−(3α−2)/(α−1)}  (e.g. ε⁻⁶ → ε⁻⁵ at α = 1.5).

This answers their explicit question whether Clip-SGD's rate is tight.

However, for unconstrained problems the same total O(ρΔG²/ε⁴ + ρΔσ^{α/(α−1)}ε^{−(3α−2)/(α−1)}) already follows from known theorems. An inexact proximal-point outer loop combined with Liu–Zhou's 2023 strongly convex clipped-SGD theorem reaches it, with no logarithms, the same random-iterate output, and the same information needs. So no complexity advantage over applicable methods is established there.

The remaining advantages are narrower. The method is a simple single loop, and the result covers constrained sets with only a projection onto X. With that oracle, the checked reduction pays (G+ρD)² instead of G² for a bounded X, and is unresolved for an unbounded X. No literature source states the selected bound, but that concerns priority, not an improved guarantee.

What can be claimed is a sharper, optimal-exponent analysis of projected Clip-SGD for weakly convex heavy-tailed problems. It does not give a better complexity for the problem class.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
