# Novelty assessment: radius-only accelerated composite (L0, L1)-smooth optimization (RadiusCompositeAccelerated)

The [theorem](../../LongTails/Theorems/RadiusCompositeAccelerated.lean) proves the following. Take the [setup](../../LongTails/Setups/RadiusCompositeGeneralizedSmooth.lean): minimize F = f + ψ over a convex Q in a real Hilbert space. Here f is convex and C¹ on all of E and satisfies the symmetric segment (L0, L1) condition, ψ is convex on Q, and the oracle returns exact gradients and an exact joint prox of ψ + ι_Q. The [algorithm](../../LongTails/Algorithms/RadiusCompositeAccelerated.lean) gets only L0, L1, R, ε and x0. It returns a feasible point x with F(x) − F(x*) ≤ ε deterministically, and no bound on F(x0) − F* is needed.

**Proved complexity** (gradient and prox calls, each counted as one; this includes initialization, rejected trials and padding):

  N = O( [ (1 + L1R)^{4/3} + √((L0 + L1G)R²/ε) ] · log²(2 + L1R + (L0 + L1G)R²/ε) ).

Here L0 > 0 and L1 ≥ 0 are the smoothness constants. R ≥ ‖x0 − x*‖ and G ≥ ‖∇f(x*)‖, both for the same minimizer x* ∈ Q. G enters only the budget, not the updates.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [CompositeGeneralizedAccelerated](../../LongTails/Theorems/CompositeGeneralizedAccelerated.lean) (2026-10-14, unpublished), composed with a one-step prox initialization (the note's reduction; I checked it only at sketch level). *Same class and oracle.* | Needs Δ ≥ F(x0) − F*. The radius-only certificate Δ ≲ (L0+L1G)e^{O(L1R)}R² gives O(√((L0+L1G)R²/ε) + (1+L1R)(1+L1R+log(1+L1G/L0))) → the bound above | (L1R)² → (L1R)^{4/3}·log². The gain needs L1R ≫ 1 and √((L0+L1G)R²/ε)·log²(2+L1R+(L0+L1G)R²/ε) ≪ (L1R)². Example: (L0+L1G)R²/ε = (L1R)² gives Θ̃((L1R)^{4/3}) vs Θ((L1R)²) | None (same instance class) | Known Δ → not needed. This is only an improvement against the reduction: if a small Δ is known, the Δ-based bound O(√(...) + L1R·log(...)) is better | Loses a log² factor on √((L0+L1G)R²/ε). Worse when (L0+L1G)R²/ε ≳ (L1R)⁴ |
| Deng–Gao, [arXiv:2512.09720v3](https://arxiv.org/html/2512.09720v3) (Jan 25, 2026, preprint), Alg. 3, Thm 6.1 and Prop. 6.2. *Direct competitor with a stronger oracle: its line search uses values of f.* | O(√(L⋆R²/ε) + log(L⋆/L_init)), with L⋆ = 2 sup of the local constant over the ball B_R(x*). Under (L0,L1), L⋆ ≲ (L0+L1G)e^{L1R}, so O(e^{L1R/2}√((L0+L1G)R²/ε)) → the bound above | Removes the factor e^{L1R/2}. The gain is substantial once L1R ≳ log(2+(L0+L1G)R²/ε). Same order up to log² when L1R ≤ 1 | None: Deng–Gao's class (any continuous local constant L(x,y), any lsc convex π with a prox) contains this one | Deng–Gao needs no L0, L1 or R. This method needs L0, L1, R and ε, and its stopping budget needs G | This method needs no function values. The bound for Deng–Gao is a substitution upper bound, not a lower bound on it |
| Rudomanov–Fomin–Gasnikov–Stonyakin, [arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461) (v1 Oct 15, v2 Nov 5, 2026, preprint), Thm 3.7. *Special case only: Q = E, ψ ≡ 0, so G = 0.* | O(√(L0R²/ε) + (1+L1R)log(2+L1R)) → O(((1+L1R)^{4/3} + √(L0R²/ε))·log²(2+L1R+L0R²/ε)) | Worse: an extra (L1R)^{1/3} factor and log² factors | Unconstrained → convex Q and/or prox-friendly ψ, with ∇f(x*) ≠ 0 allowed | None on the overlap (both radius-only) | Its lower bound (Thm 4.10, Ω(√(L0R²/ε) + L1R/√log(2+L1R))) applies to this class, which leaves an (L1R)^{1/3}·polylog gap |
| Moreau smoothing of ψ plus quadratic regularization, then Thm 3.7 above (the note's reduction, not independently verified). *Special case: Q = E and ψ globally G_ψ-Lipschitz (so G ≤ G_ψ).* | O(1 + L1R + √((L0+L1G_ψ)R²/ε) + G_ψR/ε) → the bound above | Better only when G_ψR/ε ≫ (1+L1R)^{4/3}·log²(...) and that smoothing term dominates. Otherwise worse | Lipschitz ψ, no constraints → arbitrary convex ψ and Q with a joint prox | None | None beyond the joint-prox oracle |

**Reduction check and mechanism.** For radius-only information, the routine routes cost either e^{Θ(L1R)} (a global constant, or worst-ball line searches as in Deng–Gao and [Lu–Mei, SIAM J. Optim. 33(3), 2023](https://arxiv.org/abs/2206.01209)) or (L1R)² (a gap certificate fed into the Δ-based method). The new step is the counting argument in [CompositeAdaptiveCounting](../../LongTails/Proofs/CompositeAdaptiveCounting.lean): a logarithmically weighted payment in the reverse Bregman divergence, combined with a Hölder count of the squared prox displacement. This counting, together with a bracketed trial search that does not assume monotone acceptance, gives the (L1R)^{4/3} transient. I read the energy inequality and the counting categories in the note and the module names, but I did not re-derive the constants. Proof ancestry: similar-triangles/estimate-sequence acceleration (Nesterov) and Monteiro–Svaiter large-step machinery. Neither framework supplies this composite rate.

**Search coverage.** I searched arXiv, ICML/ICLR proceedings pages and journal sources on 2026-11-12 for (L0, L1)/generalized-smooth accelerated, composite, proximal and constrained methods, including Tyurin (ICML 2026, unconstrained, Δ-based), Gorbunov et al. and Vankov et al. (ICLR 2025, unconstrained), Yu et al. (ICML 2026; its composite result is nonconvex), Lobanov 2608.04884 (unconstrained), and Frank–Wolfe variants (LMO oracle, unaccelerated). I found no prior radius-only composite bound that is polynomial in L1R. Theorem 3.7 of 2610.21461 was read only through a summarized fetch, so its exact constants and its claim of using no function values are unverified. I did not check whether a "Part II" composite version exists. The theorem was introduced in commit b1a82cbb (2026-11-12), after all cited works. The companion note's citations match what I checked. I ran no build or axiom audit.

## Conclusion

**Yes: for composite or constrained problems with only a distance bound R, the proved complexity is polynomial in L1R, where the bounds I could check or construct were exponential or quadratic.**

| Composite, radius-only, same oracle | Calls for F(x) − F* ≤ ε (log factors in the first two rows omitted) |
|---|---|
| Worst-ball line search (Deng–Gao Thm 6.1, needs function values) | e^{L1R/2}·√((L0+L1G)R²/ε) |
| Repository Δ-based method + prox gap certificate | √((L0+L1G)R²/ε) + (L1R)² |
| This result | [(1+L1R)^{4/3} + √((L0+L1G)R²/ε)]·log²(2 + L1R + (L0+L1G)R²/ε) |

The gain over the quadratic baseline survives when L1R ≫ 1 and the accuracy term times log² stays below (L1R)². For example, (L0+L1G)R²/ε = (L1R)² gives Õ((L1R)^{4/3}) versus (L1R)². The result loses in two places. When ε is small enough that (L0+L1G)R²/ε ≳ (L1R)⁴, it is a log² factor worse. And it is worse than the unconstrained radius-only optimum of Rudomanov et al. by (L1R)^{1/3} up to logarithms.

Priority is supported by my search, but that is not proof: the newest generalized-smoothness preprints are recent, and Theorem 3.7 of Rudomanov et al. was not read verbatim. The method also needs L0, L1, R and ε, while line-search competitors need none of these but query function values.

What can be claimed is the first checked radius-only accelerated guarantee for composite (L0, L1)-smooth convex optimization with polynomial (L1R)^{4/3} dependence. It improves exponential substitution bounds and the (L1R)² composition, and its optimality is unresolved.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
