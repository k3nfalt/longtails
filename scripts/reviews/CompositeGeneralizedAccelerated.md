# Novelty assessment: accelerated composite (L0, L1)-smooth optimization (CompositeGeneralizedAccelerated)

The [theorem](../../LongTails/Theorems/CompositeGeneralizedAccelerated.lean) proves the following. Take the [setup](../../LongTails/Setups/CompositeGeneralizedSmooth.lean): minimize F = f + ψ over a convex Q in a real Hilbert space, where f is convex with continuous gradient on all of E and satisfies the symmetric first-order (L0, L1) condition, ψ is convex on Q, and the prox oracle is exact. Then the gradient-and-prox similar-triangles [algorithm](../../LongTails/Algorithms/CompositeGeneralizedAccelerated.lean) returns its last iterate x_K ∈ Q with F(x_K) − F* ≤ ε, deterministically.

**Proved complexity** (3K oracle calls, each gradient or prox query counted as one):

  N = O( √((L0 + L1·G)·R²/ε) + (1 + L1·R)·log(2 + (1 + L1·R)·√(Δ/(L0·R²))) ).

Here L0 > 0 and L1 ≥ 0 are the smoothness constants. R ≥ ‖x0 − x*‖, Δ ≥ F(x0) − F*, and G ≥ ‖∇f(x*)‖, all for the same minimizer x* ∈ Q. The updates use only L0, L1, R, Δ and x0. G and ε enter only the budget, so the user needs G to know when to stop. The guarantee F(x_k) − F* ≤ R²/A_k holds at every k.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2508.06884](https://arxiv.org/abs/2508.06884) v2 (May 2026; v1 Aug 2025; ICML 2026), Thm 4.3. *Special case only: Q = ℝ^d, ψ ≡ 0, so G = 0.* | With Γ0 = 2Δ/R² and R̄ = R: O(√(L0R²/ε) + L1R·log(min{L1²Δ/L0, Δ/ε}) + log(Δ/(L0R²))) → O(√(L0R²/ε) + (1+L1R)·log(2+(1+L1R)√(Δ/(L0R²)))) | None: same order. Slightly worse logarithm when ε > L0/L1², because log(L1²Δ/L0) exceeds log(Δ/ε) | Unconstrained minimizer with ∇f(x*) = 0 → convex Q and/or prox-friendly ψ with ∇f(x*) ≠ 0 (the overlap is the special case) | None on the overlap: both need L0, L1, R and Δ (Γ0), and both bound the last iterate | 3 calls per iteration; leading constant about 10 |
| Routine reduction (my derivation): composite STM/FISTA ([Nesterov 2013](https://doi.org/10.1007/s10107-012-0629-5)) with a public global constant | O(1 + e^{L1R}·√((L0 + L1‖∇f(x0)‖)R²/ε)) → O(√((L0+L1G)R²/ε) + (1+L1R)·log(2+(1+L1R)√(Δ/(L0R²)))) | Removes the factor e^{L1R} and replaces ‖∇f(x0)‖ by G. The gain survives when e^{L1R}√(L0R²/ε) ≫ (1+L1R)·log(…), e.g. L1R = 20 and small ε. Same order when L1R ≤ 1 | None (same class) | Both have G-free updates. The baseline's budget is computable without G; this budget needs G, or a public bound that costs only e^{L1R/2} | Needs Δ (only inside the logarithm) |
| Li–Lan AC-FGM, [arXiv:2310.10082](https://arxiv.org/abs/2310.10082) v3 (Math. Program.), Thm 1 / Cor. 1 and Remark on local smoothness. *Direct competitor with a stronger oracle.* | 12·L̂_k·(‖z0−x*‖²/β + …)/k², where L̂ is the largest curvature estimate along a bounded trajectory → this result | Not comparable: under (L0, L1), L̂ is bounded only by (L0+L1G)·e^{O(L1·r)}, with r the trajectory radius; no explicit bound in the original parameters is given | None (composite with closed X and prox h) | AC-FGM needs no L0, L1, R, Δ or G, in updates or stopping. This method needs L0, L1, R and Δ | AC-FGM needs function values (its estimates L_t), which this oracle model does not provide |

**Reduction check and mechanism.** STM on (f, ψ) runs exactly like STM on the shifted function h = f − ⟨g*, ·⟩ with ψ' = ψ + ⟨g*, ·⟩, and h is (L0 + L1G, L1)-smooth with ∇h(x*) = 0. So the ∇f(x*) issue is not hidden from the algorithm. However, no published composite version of an unconstrained (L0, L1) acceleration analysis exists, and the constant L0 + L1G is unknown. Without the observed-constant cocoercivity bound, the routine routes pay e^{L1R}. That bound, ‖∇f(x) − g*‖² ≤ 8(M(x) + L1‖∇f(x) − g*‖)·h(x) with M(x) = L0 + L1‖∇f(x)‖ (`shifted_cocoercive`), together with the growth cap a_k ≤ A_k/(1 + 32L1R), is the new step I verified in the Lean source. Proof ancestry: the similar-triangles template, Nesterov's composite gradient mapping, and the shift lemma (stated as Prop. 1 in [Vyguzov–Stonyakin 2609.00261](https://arxiv.org/abs/2609.00261) for its subproblems). None of these supplies the composite rate.

**Other checked work.** Several papers do not cover the target class:
- [Yu et al. 2502.00753](https://arxiv.org/abs/2502.00753) v3 (ICML 2026), Thm 3.7: Assumption 2.5 requires f to be closed on an open domain, which puts the minimizer at a point with ∇f(x*) = 0. Its composite result (Thm 5.1) is nonconvex and bounds the gradient mapping.
- Gorbunov et al. and Vankov et al. (ICLR 2025): unconstrained.
- Richtárik–Gruntkowska–Li 2605.08850: unaccelerated, and the step size needs ‖∇f(x*)‖.
- Vyguzov–Stonyakin 2609.00261: an inner solver for unconstrained minimizers.
- Lobanov 2608.04884: a different, unconstrained smoothness class.

The note's lower-bound example satisfies the class assumptions, but its span argument with prox queries was not rigorously checked. I did not run a build.

**Search coverage.** Searched on 2026-10-07: arXiv and proceedings/journal pages for (L0, L1)/generalized-smooth acceleration, constrained and composite variants, and line-search-free accelerated methods. The theorem was introduced in commit 8aaaa18 (2026-10-03), and all compared works predate it. I did not read the full ICML 2026 texts or the Lu–Mei (SIAM J. Optim. 2023) proofs. The companion note's citations match what I checked. Its claim that the method "never uses G" holds for the updates only, not for the stopping budget.

## Conclusion

**Yes: on constrained and composite problems, the proved complexity is exponentially better than the guarantees I could construct or check for the same oracle.**

| | Oracle calls for F(x) − F* ≤ ε |
|---|---|
| Accelerated prox with public global constant | O(e^{L1R}·√((L0+L1‖∇f(x0)‖)R²/ε)) |
| This result | O(√((L0+L1G)R²/ε) + (1+L1R)·log(2+(1+L1R)√(Δ/(L0R²)))) |

The strongest prior (L0, L1) accelerated analysis, Tyurin's Theorem 4.3, needs an unconstrained minimizer. On that overlap the two bounds match up to logarithms, so the gain is the new composite setting: it covers Q and ψ with ∇f(x*) ≠ 0, such as constrained exponential-loss problems. In that setting the factor e^{L1R} disappears whenever L1R is more than a constant. When L1R ≤ 1, there is no gain.

What remains uncertain: function-value methods such as AC-FGM are parameter-free, but their (L0, L1) bounds were not derived, and I found no polynomial bound for them. The method needs Δ, L0, L1 and R, and it needs G to stop. Separately, my search found no earlier accelerated composite (L0, L1) objective-gap guarantee. That is evidence of priority, not proof.

The contribution that can be claimed is the first checked accelerated objective-gap guarantee for constrained/composite (L0, L1)-smooth convex problems that avoids exponential factors, together with the observed-constant analysis that makes it work.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
