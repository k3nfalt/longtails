# Novelty review: stochastic nonsmooth hidden-convex optimization

The [theorem](../../LongTails/Theorems/NonsmoothHiddenConvexStochastic.lean) builds a restarted, ball-projected dual-averaging method ([algorithm](../../LongTails/Algorithms/NonsmoothHiddenAveraging.lean)). For every instance of the [setup](../../LongTails/Setups/NonsmoothHiddenConvex.lean), it proves that the method's final epoch center x̂ satisfies `∫ F(x̂) − F(x⋆) dP ≤ ε`. Here `F = H∘c` on a finite-dimensional space, `H` is convex and finite, and `c` is a C¹ homeomorphism with `μ‖x−y‖ ≤ ‖c(x)−c(y)‖ ≤ L_c‖x−y‖` and an `L_J`-Lipschitz Jacobian. The algorithm uses unbiased IID stochastic pulled subgradients with second moment at most `G²`, a known radius `R` with `F(0) ≤ F(y)` whenever `‖y‖ = R`, and an attained minimum.

**Proved oracle complexity.** The budget is the Lean formula `⌈10¹⁰·W·log³(10¹⁰(2+W))⌉`, where

  W = (1 + 64 L_J R/μ)·(L_c/μ + G² L_c³ R²/(μ³ ε²)),

which is `O(W·log³(2+W))`. The parameters are `μ, L_c` (bi-Lipschitz constants of the hidden map), `L_J` (Jacobian Lipschitz constant), `G` (oracle second-moment bound), `R` (barrier radius, which implies `‖x⋆‖ ≤ R`), and `ε` (target expected gap). The updates need all of these parameters; `F(0)−F⋆` is not needed. In the nontrivial regime `ε < GR` (note that `F(0)−F⋆ ≤ GR`), the bound is `Õ((1+L_JR/μ)·G²L_c³R²/(μ³ε²))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Bhaskara–Cutkosky–Kumar–Purohit, [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/c40fc068ed2b4ad43bff4f3f3206691e-Paper-Conference.pdf), §5, (A3), Thm 5.4 (direct competitor, prior). Rescale `P = c/μ`, which gives `α = μ/L_c`, `β = 1`, `ρ = L_J/μ`, `H = G`; their condition `D₂² ≥ αβ/ρ` forces `ρ' = max(L_J/μ, μ/(L_cR²))`. | `O(G³R⁴L_c⁴ρ'/(μ⁴ε³))` → `O(W log³(2+W))` | Leading order improves from `ε⁻³` to `ε⁻²`. For `L_JR ≥ μ`, the speedup is about `G L_c R/(μ ε)` up to `log³`; for `L_JR < μ`, it is at least `GR/ε`. The gain survives when `GR/ε ≫ log³(2+W)`. | A.s. oracle bound `‖h‖ ≤ H` → second-moment bound `E‖g‖² ≤ G²`. Their two-sphere ordering with `D₁ = 0` (restart to 0) appears to be exactly the present barrier, so the localization assumption is not substantively weakened. | None: both output the final restart center with an expected gap, and both need known parameters. | None found on this overlap. Both require a finite-dimensional unconstrained bi-Lipschitz `c` with a Lipschitz Jacobian. |
| SGD for convex Lipschitz `F` (Nemirovski–Yudin; e.g. [Bubeck, Thm 6.1](https://arxiv.org/abs/1405.4980)), special case `L_J = 0` only (`c` affine, so `F` is convex) | `O(G²R²/ε²)` → `O((L_c/μ + G²L_c³R²/(μ³ε²))·log³(…))` | **Worse** by a factor of `(L_c/μ)³·log³` on this overlap. | None | None (an averaged SGD iterate vs. the restart center; both give an expected gap) | The hidden-convex method pays for conditioning even when the map is affine. |
| Fatkhullin–He–Hu, [arXiv:2401.00108v2](https://arxiv.org/abs/2401.00108v2) (SIOPT 2025), §4.1, Thm 2 / Cor 1 (prior). Applies only when `X` is closed and convex and `U = c(X)` is convex and bounded. | `Õ(ε⁻³)` for the Moreau-envelope gap. Their Lipschitz conversion gives the iterate's own gap `≤ ε + G√(ε/ℓ)`, i.e. `Õ(ε⁻⁶)`. → not comparable | Not comparable: the unconstrained target has `U = E` (`D_U = ∞`), and no verified reduction to a bounded convex `U` exists. | Incomparable: constrained, possibly nonsmooth-`c` classes vs. unconstrained global problems with a barrier | None | Theirs needs bounded `c(X)`; the present result needs a barrier radius and a global diffeomorphism. |

**Reductions and mechanism.** I checked the obvious reduction. `F` is `ℓ`-weakly convex with `ℓ = GL_J/μ`, and an inexact proximal-point method with the hidden comparator `c⁻¹((1−t)c(x)+tc(x⋆))` forces the prox weight to be at least `ℓ`. The comparator penalty `ℓt²L_c²R²/μ²` must stay below `tε`, so `t ≤ μ³ε/(GL_JL_c²R²)`. That gives `1/t` outer steps, each a `tε`-accurate strongly convex subproblem costing `G²/(ℓtε)` calls, and reproduces only `ε⁻³`, which matches the FHH and BCKP rates. Batching or clipping does not remove this distortion. The new ingredient is a local energy analysis of averaged dual steps that carries the never-evaluated Taylor corrector `q(x,u)`. It gives a `√N` local rate for an arbitrary comparator in a ball of radius `R/(1+64L_JR/μ)`. Proof ancestry: Cutkosky's anytime averaging and BCKP's ball-epoch/restart architecture supply the outer scheme. The FHH comparator interpolation supplies the epoch contraction. Neither supplies the local `ε⁻²` estimate. Other related work covers only strict subclasses with different oracles: [Barakat et al. 2026](https://arxiv.org/abs/2605.26373) (online OGD; Hessian-compatible `q`, bounded domain, exact gradients) and [Chen–He–Hu–Ye](https://arxiv.org/abs/2205.01774v3) (MSG; coordinate-wise separable `φ`, smooth `f`, bounded box). Neither covers non-separable, non-Hessian-compatible nonsmooth instances. The repository's [smooth accelerated hidden-convex theorem](../../LongTails/Theorems/HiddenConvexAcceleratedStochastic.lean) requires smooth `F`.

**Search coverage.** The search ran on 2026-10-29 UTC over arXiv, ICLR 2025 proceedings and SIOPT/arXiv versions of FHH, plus general web searches for later work citing BCKP. I read the theorem statements of BCKP Thm 5.4, FHH Thm 2/Cor 1, Barakat et al. Assumptions 1–3/Thm 1 and Chen–He–Hu–Ye Assumption 2.1. I did not exhaustively scan NeurIPS 2025/ICML 2026 proceedings. The result was introduced in commit `da7e286` (2026-10-29). The companion note's claim that the barrier is "weaker than A3" is overstated: A3 with `D₁ = 0` appears identical.

**Conclusion**

**Yes: against the only direct prior competitor, the accuracy dependence improves from ε⁻³ to ε⁻², up to logarithms.** BCKP (ICLR 2025, Thm 5.4) covers the same unconstrained bi-Lipschitz, Lipschitz-Jacobian model and explicitly lists ε⁻² as an open question.

| | expected-gap oracle calls |
|---|---|
| BCKP | `O(G³R⁴L_c⁴·max(L_J/μ, μ/(L_cR²))/(μ⁴ε³))` |
| This result | `O((1+L_JR/μ)(L_c/μ + G²L_c³R²/(μ³ε²))·log³(…))` |

When `L_JR ≥ μ`, the gain factor is about `GL_cR/(με)`; otherwise it is at least `GR/ε`. In both cases the gain needs `ε` below `GR/polylog`. The oracle assumption also weakens from almost-sure bounded to second-moment bounded. The localization barrier is essentially BCKP's own.

The result loses when `L_J = 0`. There plain SGD needs `O(G²R²/ε²)`, so this method is worse by `(L_c/μ)³`. The dependence on conditioning is likely far from optimal, and no lower bound shows that ε⁻² is the right exponent once the geometry factors are included.

The comparison proves the gain; my literature search did not find an earlier or concurrent ε⁻² result for this class, but it was not exhaustive. The claimable contribution is a nonsmooth stochastic hidden-convex guarantee at `Õ(ε⁻²)` without any Hessian-compatibility or separability assumption, answering BCKP's open question in their own model.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
