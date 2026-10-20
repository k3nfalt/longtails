# HiddenPotentialOracleComplexity: novelty assessment

The [theorem](../../LongTails/Theorems/HiddenPotentialOracleComplexity.lean) proves the following. Let F be μ-strongly monotone on a real Hilbert space, and suppose F = ∇φ + S for some unknown φ with L-Lipschitz ∇φ and some s-Lipschitz S. Assume a root x⋆ exists with ‖x₀ − x⋆‖ ≤ R. Then the deterministic nested proximal/accelerated method [`hiddenPotentialOutput`](../../LongTails/Algorithms/HiddenPotential.lean) queries only F(x) and returns x_out with ‖x_out − x⋆‖ ≤ ε ([setup](../../LongTails/Setups/HiddenPotentialStronglyMonotone.lean)).

**Complexity.** The budget is ⌈2²¹√((μ+s)(L+μ+s))/μ · log(2+s/μ) · log(2+R/ε)⌉. Since F is (L+s)-Lipschitz and μ-strongly monotone, L+s ≥ μ, so the budget is

  K = O( √((μ+s)(L+s))/μ · log(2+s/μ) · log(2+R/ε) ),

for μ > 0, L, s, R ≥ 0 and ε > 0. Here μ is the strong-monotonicity modulus of F, L is the Lipschitz constant of the hidden gradient part, s is the Lipschitz constant of the hidden residual, R bounds the initial distance, and ε is the target distance accuracy. The theorem does not require φ to be convex or S to be monotone.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Past extragradient, [Gidel et al., ICLR 2019, arXiv:1802.10551](https://arxiv.org/abs/1802.10551), Thm 1 (one F-call per step, ‖ω_t−ω⋆‖² ≤ (1−μ/4L_F)^t R²), with L_F = L+s. Direct competitor: same class, same oracle, same criterion. | O(1 + (L+s)/μ · log(2+R/ε)) → K | Factor √((L+s)/(μ+s)) / log(2+s/μ). It is a gain when L+s ≫ (μ+s)·log²(2+s/μ). Examples: at s ≤ μ, κ log → √κ log, where κ = L/μ. At s = √(Lμ), κ → κ^{3/4} log κ. | None. Extragradient covers the whole class, since it needs only Lipschitz continuity. | None. Both give a deterministic last-output distance guarantee, and both need μ, L, s (or L_F) for their parameters. | Worse by a log(2+s/μ) factor when s ≳ L. The method needs L and s separately, not just L+s. |
| [Wang–Li, NeurIPS 2020, arXiv:2006.06359v2](https://arxiv.org/abs/2006.06359), Thm 3. Special-case baseline: strongly-convex–strongly-concave (SC-SC) saddles with a public x/y partition and a joint gradient (= combined F). The classes overlap on bilinear coupling (μ_x=μ_y=μ, L_x=L_y=L, L_xy=s) and are otherwise incomparable. | O(√(L/μ + Ls/μ²) · ln³(L̄²/μ²) · ln(L̄²R/(μ²ε))), with L̄ = max(L,s) → K | On the overlap the polynomial order is the same. K is better by logarithms: about ln²(L̄/μ) and the condition number inside the accuracy log. | Public partition with an SC-SC structure → hidden, arbitrary decomposition of a general monotone field. Fields with nonlinear S and no block structure become covered. Wang–Li's nonlinear-coupling instances are not covered. | None. Both give a distance guarantee for the last output. | The hidden class does not contain Wang–Li's general nonlinear-coupling class. |
| [Kovalev–Gasnikov–Richtárik, NeurIPS 2022, arXiv:2112.15199](https://arxiv.org/abs/2112.15199), Thm 4.2/§5.1 (APDG). Special case: bilinear coupling with a public partition. There, ∇f, ∇g, Ax and Aᵀy can be recovered from F(x,0), F(0,y) and F(0,0), at ≤ 3 combined calls each. | O((√(L/μ) + s/μ) · log(C/ε)), with C left unexpanded in the theorem and a squared-distance criterion → K | Worse: for μ ≪ s ≪ L, √(Ls)/μ versus √(L/μ) + s/μ. | Same as the previous row: hidden partition and nonlinear S → covered. | None. | APDG needs the public partition plus component strong convexity. Without the partition, this reduction is unavailable. |
| [Yuan et al., NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/file/69ce18ad9f53f28e8e7ac1649ae02337-Paper-Conference.pdf), Cor. 2.8 (restarted AG-EG, zero noise). Stronger oracle: separate ∇φ and S. | O((√(L/μ) + s/μ) · log(R/ε)) with split access → K with combined access | Not comparable: the oracles differ. Split access is better whenever μ ≪ s ≪ L. | Requires a strongly convex φ and a monotone S → neither is required here. | None. | This result's advantage is weaker oracle access: only F, with the decomposition never revealed. |

**Reduction check.** The upper bound composes standard tools. An inexact proximal point step with regularization β = 512s contracts by 1 − μ/(2(μ+β)) per step. Each step is solved by projected AGD, treating S frozen at the ball centre as a bounded gradient error ([d'Aspremont 2008](https://www.di.ens.fr/~aspremon/PDF/SmoothSparseSDP.pdf)), with radius halving. Wang–Li use the same idea of regularizing at the coupling scale, with accelerated inner solves. Applying it to a hidden decomposition works because only S needs to be small relative to β. I found no reduction that gives this bound from a published theorem without redoing that analysis.

The companion note's main claim is a combined-versus-split separation. Its lower bound (`combined_oracle_lower_bound`: deterministic algorithms only, dimension 8N+14, regime μ ≤ s ≤ L/4) sits in a proof module, not in the selected theorem. I did not verify it, and it does not count as part of this assessment.

**Search coverage.** I searched on 2026-10-20 UTC. The result was introduced in commit 193338b on that same date. Sources were arXiv, NeurIPS/ICLR/ICML proceedings, and theorem statements from Wang–Li, Kovalev et al., Yuan et al. and Gidel et al. I did not inspect Lee–Ryu–Yun (arXiv:2604.11105), Spillane–Szyld (a linear Krylov analysis), or Chen–Lan–Ouyang's AMP (split access). I found no prior combined-oracle theorem for this hidden class. That is not proof of priority. The note's citations I checked agree with the Lean statement.

## Conclusion

**Yes, but modestly: for unknown gradient-plus-small-residual fields, the result beats extragradient, while its rate and mechanism are already known for public saddle structure.**

The strongest applicable competitor on the full class is extragradient, which uses the same combined oracle:

| | Combined-oracle calls |
|---|---|
| Extragradient | (L+s)/μ · log(2+R/ε) |
| This result | √((μ+s)(L+s))/μ · log(2+s/μ) · log(2+R/ε) |

The gain is √((L+s)/(μ+s))/log(2+s/μ). It is real when L+s ≫ (μ+s)·log²(2+s/μ). For example, with s ≈ μ the cost drops from κ to √κ, where κ = L/μ. When s ≳ L it loses a log(2+s/μ) factor.

What is new is the problem setup: only F is available, and the potential/residual split is unknown and arbitrary. On bilinear saddles with a public x/y split, Wang–Li (2020) already reach the same √(L/μ + Ls/μ²) order with joint gradients. Recovering the separate components there then allows the better √(L/μ) + s/μ. So the gain over extragradient comes from a fairly routine composition: proximal regularization at the scale of s plus inexact acceleration. Its significance depends on how much the hidden-decomposition model matters in practice.

The claimable contribution is a combined-oracle upper bound for hidden-potential strongly monotone fields that improves on extragradient when s ≪ L. The more interesting separation claim depends on the lower bound, which is not part of this theorem.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
