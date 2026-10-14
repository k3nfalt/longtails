# AdjointAcceleratedCohypomonotone: novelty assessment

[`result`](../../LongTails/Theorems/AdjointAcceleratedCohypomonotone.lean) proves the following. Take any L-Lipschitz, ρ-cohypomonotone F on a finite-dimensional space, with an L₂-Lipschitz Jacobian and a zero x* satisfying ‖x0 − x*‖ ≤ R. Running [`adjointAccelerated`](../../LongTails/Algorithms/AdjointAcceleratedProximal.lean) for `budget` deterministic calls to F(x) and DF(x)ᵀw returns its last completed outer iterate x̂ with ‖F(x̂)‖ ≤ ε. This holds for every ρ ≥ 0, L₂ ≥ 0 and ε > 0 ([setup](../../LongTails/Setups/CohypomonotoneAdjoint.lean)).

**Complexity.** Here L is the Lipschitz constant of F, L₂ the Lipschitz constant of its Jacobian, ρ the cohypomonotonicity parameter, R the initial distance to a zero, and ε the residual target. Substituting into the proved budget (with (1+2ρL)²(2+2ρL)³ ≍ (1+ρL)⁵) gives

  O( (LR/ε + 1 + ρL)·log(2+ρL) + (1+ρL)⁵·log(2+ρL)·(L₂R/L)·log²(2+LR/ε) ).

The updates use L, L₂ and ρ. R and ε enter only the budget.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Alacaoglu–Kim–Wright, ICML 2024, Thm 2.1/Cor 2.2 ([arXiv 2402.05071](https://arxiv.org/abs/2402.05071), v3 2026). *Applies only when ρL < 1.* | With η = (ρ+1/L)/2: O(LR/((1−ρL)²ε)·log(2+LR/((1−ρL)ε))) → on ρL<1: O(LR/ε + (L₂R/L)·log²(2+LR/ε)) | Speedup ≈ (1−ρL)⁻²·log when L₂R/L·log²(2+LR/ε) ≤ LR/((1−ρL)²ε); otherwise the burn-in can dominate | ρL < 1 → any ρ ≥ 0 (only with the extra assumptions in the last column) | None. Both bound the residual at the output; Remark 2.3's resolvent residual is within factor 1+ηL ≤ 2 of ‖F‖ | Needs an L₂-Lipschitz Jacobian and DF(x)ᵀw access; loses AKW's constraints/G and stochastic results; adds the L₂ burn-in term |
| Repository sibling [AdjointAnchoredCohypomonotone](../../LongTails/Theorems/AdjointAnchoredCohypomonotone.lean) (unpublished; same commit 32aa939). *Identical setup.* | O(((1+ρL)LR/ε + (1+ρL)²)·log(2+ρL) + (1+ρL)⁴(L₂R/L)·log²(2+LR/ε)) → selected bound | Leading term smaller by a factor ≈ 2(1+ρL); the total bound improves when ρL ≥ 1 and ε ≤ L²/(41(1+ρL)²(1+2ρL)²L₂(4+log(1+4LR/ε))²) (I checked this condition) | None | None | Burn-in worse by a factor ≈ 5(1+ρL)·log(11+10ρL), so the sibling bound is smaller for larger ε |
| CGLS/LSQR (Krylov method on the normal equations). *Applies only to affine F (L₂ = 0), the note's own example class.* | ≈ LR/ε + 2 → O(LR·log(2+ρL)/ε + (1+ρL)·log(2+ρL)) | Worse by a log(2+ρL) factor | None on this overlap. CGLS needs no cohypomonotonicity | None | Same oracle (Mp = F(p) − F(0), Mᵀw is one adjoint call). Chebyshev bound ‖r_k‖ ≤ LR/(2k+1), which I derived myself |

**Standard-reduction check.**
- The outer loop is an inexact Halpern/anchored iteration on J_{γF} with γ = 2ρ + 1/L. AKW's outer analysis only needs η > ρ; their requirement η < 1/L comes from the F-only inner solver.
- With adjoint access and γ ≥ 2ρ, the inner problem v + γF(v) = t becomes a nonlinear least-squares problem. Its Jacobian has singular values in [1, 1+γL].
- From there, two textbook results take over. PL gradient descent gives the sibling's Λ² inner cost. Local strong convexity with κ = 4Λ² plus AGD, as in Catalyst/Monteiro–Svaiter, gives the selected Λ·log cost.
- I did not verify line by line that AKW's outer lemma holds verbatim for η ≥ 1/L. The genuinely technical additions are AGD region invariance in a nonconvex merit (`agd_region`) and charging fallback loops to summable residuals.

**Search coverage (2026-10-14).**
- Searched arXiv, ICML/NeurIPS proceedings and Google for cohypomonotone, weak-MVI, negative-comonotone, higher-order and Jacobian-based methods. Sources checked: AKW Thm 2.1; Gorbunov et al., ICML 2023 (exact proximal point, resolvent oracle, not comparable); Tran-Dinh 2025; Alomar–Chavdarova 2024; Perseus.
- I found no published guarantee for ρL ≥ 1 and no lower bound showing the 1/L barrier for F-only methods. Not finding a competitor does not prove one doesn't exist.
- The companion note's citations match. However, the note does not mention that standard Krylov methods beat its bound on its own affine example. Its comparison baseline is an unpublished sibling, and the two were introduced in the same commit, so their order of development is unknown.

**Conclusion**

**The leading term improves by a factor of about (1+ρL) over the repository's unpublished sibling, at small ε; the access to ρL ≥ 1 comes from the stronger oracle, not from this theorem.**

Published methods (Alacaoglu–Kim–Wright, ICML 2024) use F alone and need ρL < 1. With Jacobian-adjoint access and a Lipschitz Jacobian, both repository theorems handle every ρ:

| | ε-dependent term | burn-in |
|---|---|---|
| sibling | (1+ρL)·LR/ε·log(2+ρL) | (1+ρL)⁴·(L₂R/L)·log²(LR/ε) |
| this result | LR/ε·log(2+ρL) | (1+ρL)⁵·log(2+ρL)·(L₂R/L)·log²(LR/ε) |

The gain survives only when ε ≲ L²/((1+ρL)⁴L₂·log²(LR/ε)). For larger ε the sibling's bound is smaller. On affine instances, the plain normal-equations Krylov method needs about LR/ε calls, which beats both.

The comparison shows a real gain over the sibling. The literature search found no published ρL ≥ 1 guarantee, but that broader scope is shared with the sibling. It follows from an apparent composition of known pieces: an AKW-type anchored outer loop, plus the observation that, with adjoint access, the resolvent subproblem is a well-conditioned least-squares problem. The selected theorem's own increment is accelerating that inner solve with AGD, which is Catalyst-style. The new technical work is a region-invariance argument; I did not check the outer-lemma reduction for γ ≥ 1/L line by line.

What can be claimed is an accelerated inner solver that removes one (1+ρL) factor in the small-ε regime for this adjoint-oracle setting. That is not a new problem class or a new rate barrier.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
