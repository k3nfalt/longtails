# Novelty assessment: `CompositeImplicitTransport`

[`result`](../../LongTails/Theorems/CompositeImplicitTransport.lean) proves the following for the [setup](../../LongTails/Setups/StochasticCompositeHessianLipschitz.lean) `F = f + ψ` on a convex set `Q ⊆ E` (finite-dimensional). Here `∇f` is `L`-Lipschitz, `∇²f` is `ρ`-Lipschitz on all of `E`, and `ψ` is convex on `Q` with an exact prox. The [prox-transport algorithm](../../LongTails/Algorithms/CompositeTransport.lean) uses one unbiased, variance-`σ²` IID stochastic gradient per step and outputs a uniformly random iterate `x_τ ∈ Q` with `E‖L(x_τ − prox_{1/L}(x_τ, ∇f(x_τ)))‖ ≤ ε`.

**Proved complexity.** The budget is `n₀ + 2T`, counting both gradient and prox calls, with `n₀ = ⌈1080σ²/ε²⌉+1` and `T = ⌈9Δ/ε²·(L + 7√(ρε/3)(1+1080σ²/ε²))⌉`. This gives

  N = O( LΔ/ε² + Δ√ρ ε^{-3/2} + σ²√ρ Δ ε^{-7/2} + σ²/ε² + 1 ),

valid for `L, ε > 0` and `ρ, σ, Δ ≥ 0`. The parameters are:
- `Δ`: a bound on `F(x₀) − inf_Q F`;
- `L`: the gradient-Lipschitz constant;
- `ρ`: the Hessian-Lipschitz constant;
- `σ²`: the noise variance.

All of these parameters are needed for tuning.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gao–Rodomanov–Stich, Polyak-momentum prox-SGD, [ICML 2024 / arXiv 2403.02967](https://arxiv.org/abs/2403.02967), Thm. 1 & App. F–G (squared criterion `E‖·‖² ≤ ε²`, converted via Jensen) | `O(LΔσ²/ε⁴ + LΔ/ε² + σ²/(LΔ))` → `N` | Noise term `LΔσ²ε⁻⁴ → √ρΔσ²ε^{-7/2}`, a factor `L/√(ρε)` smaller. The total gains when `ρε ≪ L²` and `σ ≳ ε`. **Worse** by a factor `√(ρε)/L` when `ρε > L²`. | None (GRS needs no Hessian regularity) | None: both use a random iterate, single sample, and known parameters | Adds a global `ρ`-Lipschitz Hessian on all of `E`, not just `Q`, and needs `ρ` to be known |
| Cutkosky–Mehta NIGT, [ICML 2020 / arXiv 2002.03305](https://arxiv.org/abs/2002.03305), Thm. 3. **Special case ψ = 0, Q = E**, where `G = ∇f` | `O(LΔ/ε² + √ρΔσ²ε^{-7/2} + σ^{13/3}Δ^{-4/3}ρ^{-2/3}ε^{-7/3})` → `N` | None: the leading terms are the same order. The lower-order terms are incomparable. | `ψ = 0` → any convex prox-friendly `ψ` on convex `Q` (ℓ₁, box or simplex indicators, unbounded `Q`) | None: both give an averaged or random iterate of `E‖·‖` | None on the overlap; there the prox is the closed-form step `x − γv` |
| He–Deng SIPM-EM, [JMLR 26 (2025)](https://jmlr.org/papers/v26/24-2158.html), Thm. 19, Remark 20. **Different class**: `Ax=b`, `x ∈ K` | `Õ(ε^{-7/2})` iterations on a barrier-scaled residual → `N` | Not comparable: their criterion is weaker near the boundary | Incomparable: they handle cones, affine constraints, and a locally Lipschitz Hessian; this result handles a nonsmooth `ψ` with a global Hessian bound | Unscaled gradient mapping vs. scaled residual. Polylog factors removed. | Needs a prox of `ψ` instead of a barrier |
| Jang–Lee LMO-IGT, [arXiv 2605.05577](https://arxiv.org/abs/2605.05577) (May 2026 preprint). **Compact `C`, LMO oracle** | `O(ε^{-7/2})` on the averaged Frank–Wolfe/support gap → `N` | Not comparable: different oracle and criterion. Turning their gap into a gradient-mapping bound costs `ε^{-7}`. | Compact `C` → unbounded `Q` and general `ψ` | Gap → gradient mapping | Needs a prox rather than an LMO |

**Reduction and mechanism.** I found no reduction that gives this bound:
- Cutkosky–Mehta's normalized step has no composite analogue.
- Moreau-envelope or smoothing reductions destroy the Hessian-Lipschitz structure.
- He–Deng and Jang–Lee use other constraint models.

The proof combines three known ingredients:
- implicit gradient transport (Arnold et al. 2019; Cutkosky–Mehta), which provides the `ρ‖Δx‖²/α` bias bound;
- bounded per-step movement, also used by He–Deng (Dikin steps) and Jang–Lee (LMO steps);
- standard gradient-mapping monotonicity.

The new step is the "capped composite descent" inequality: a step capped at `2γε'` is still a convex combination, which keeps the iterate in `Q`, and the inequality gives descent that is linear in `‖p−x‖` in both the capped and uncapped branches.

**Search coverage (2026-11-09).** I searched the web for stochastic composite, proximal, and constrained methods with a Lipschitz Hessian at rate `ε^{-7/2}`, IGT variants, and LMO/Frank–Wolfe and interior-point variants. Coverage and caveats:
- [RanSOM (arXiv 2602.06824)](https://arxiv.org/abs/2602.06824) uses Hessian-vector products and reaches `ε⁻³`, so it is a stronger oracle and was excluded.
- The GRS and Jang–Lee theorem statements were read only through partial extracts.
- The companion note's lower bound, Arjevani et al. ([arXiv 2006.13476](https://arxiv.org/abs/2006.13476), eq. (10)), is stated inside a minimum with `ΔLσ²ε⁻⁴`, for `ψ = 0` and zero-respecting algorithms. It therefore supports optimality of the noise term only when `ε ≲ L²/ρ`.
- He–Deng's introduction (§1.3) credits Cutkosky–Mehta with `ε^{-7/2}` for projection-constrained problems. Cutkosky–Mehta's Theorem 3 is unconstrained, so this looks like an imprecise citation and not a prior proof, but it shows the extension was widely expected.

**Conclusion**

**Yes: this gives the first `ε^{-7/2}` single-sample guarantee I could find for general prox-friendly composite problems, but the gain is a scope extension of a known rate.**

Under a Lipschitz Hessian, Cutkosky–Mehta already reach this order for `ψ = 0`. For composite problems, the strongest applicable first-order baseline I found is Gao–Rodomanov–Stich, which assumes only `L`-smoothness:

| | Total calls for `E‖G‖ ≤ ε` |
|---|---|
| Gao–Rodomanov–Stich (composite) | `LΔσ²ε⁻⁴ + LΔε⁻²` |
| This result | `LΔε⁻² + σ²√ρΔε^{-7/2} + Δ√ρε^{-3/2} + σ²ε⁻²` |

The noise cost improves by a factor `L/√(ρε)` when `ρε ≪ L²` and `σ ≳ ε`. The new bound is worse when `ρε > L²`. The price is a globally Lipschitz Hessian on all of `E`, plus knowledge of `ρ`.

The comparison establishes this gain over the checked baselines. Priority is less certain: the interior-point and LMO analogues, and He–Deng's informal attribution, show the extension was expected and its ingredients were known. Still, I found no prior proof for the prox setting with the unscaled gradient-mapping criterion. A missed preprint could change the priority claim, but not the comparison.

The claimable contribution is a proof that implicit gradient transport, combined with movement capping, extends the optimal-order `ε^{-7/2}` stochastic rate from unconstrained problems to general prox-friendly composite problems.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
