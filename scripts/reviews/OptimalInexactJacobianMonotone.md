# Novelty assessment: OptimalInexactJacobianMonotone

[`result`](../../LongTails/Theorems/OptimalInexactJacobianMonotone.lean) proves the following for every monotone, differentiable `F` on a finite-dimensional real inner-product space with `M`-Lipschitz Jacobian and a root within `R` of `x₀` ([setup](../../LongTails/Setups/InexactJacobianMonotone.lean)). Given an oracle that returns the exact `F(x)` and some `J` with `‖J − DF(x)‖ ≤ δ` (adversarial and history-dependent), the [nested anchored algorithm](../../LongTails/Algorithms/NestedAnchoredInexactJacobian.lean) returns its last accepted outer iterate, and this iterate satisfies `‖F(output)‖ ≤ ε` on every path.

**Proved budget.** The budget is `⌈2²²(1 + (MR²/ε)^{2/5} + δR/ε)⌉`, that is,

  N = O(1 + (MR²/ε)^{2/5} + δR/ε) combined (F, J) calls,

where M is the Jacobian Lipschitz constant, R bounds ‖x₀ − x*‖, δ bounds the Jacobian error and ε is the residual target. It holds for M, R, ε > 0 and δ ≥ 0. The algorithm needs to know M, δ, R and ε. There is no logarithmic factor. The model is a "unit call" model: each call returns one F-value and one Jacobian, and linear solves are free. The commit dates the result to 2026-11-04.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jiang–Yoon, [arXiv 2609.30212v1](https://arxiv.org/abs/2609.30212) (24 Sep 2026, prior), Thms 4.4, 4.6. **Covers only the special case δ = 0.** | O((1+(MR²/ε)^{2/5})(1+log(1+MR²/ε))) → O(1+(MR²/ε)^{2/5}) | Saves a factor log(1+MR²/ε). This matters when MR²/ε ≫ 1 | Exact Jacobian → δ-inexact Jacobian (the δR/ε term is new for this criterion) | None. Both use a last-iterate residual and known parameters | Jiang–Yoon also handles composite inclusions with tangent residual. This result is restricted to equations F = 0. Its constant 2²² is very large |
| Zhang et al., [arXiv 2609.23557v1](https://arxiv.org/abs/2609.23557) (20 Sep 2026, prior), Thms 3.1, 5.1. **Exact Jacobian, compact convex X.** | O((MR²/ε)^{2/5}), log-free on compact X → O(1+(MR²/ε)^{2/5}+δR/ε) on all of E | Not comparable. The unconstrained case is not covered; embedding the problem in a ball is unchecked (see below) | Compact X → full space without a domain bound; exact → δ-inexact | None | They cover constrained VIs, which this result does not |
| Agafonov et al., NeurIPS 2024 ([2405.15990v2](https://arxiv.org/html/2405.15990v2)), Thm 3.2; restarted method in Thm 6.2. **Bounded domain, gap criterion.** | Gap: O((MD³/ε)^{2/3}+δD²/ε) calls, plus bisection inside each step → residual O(1+(MR²/ε)^{2/5}+δR/ε) | Not comparable: weak (Minty) gap vs residual, and diameter D vs distance R | Bounded domain + gap → unbounded domain + residual | Averaged/weak solution → last-iterate strong residual | Same δ-error model (their Assumption 2.1). They also give quasi-Newton instantiations |
| Inferred composition, not published: anchored/Halpern outer loop + VIJI-Restarted (their Thm 6.2) for the inner subproblem + radius doubling | Õ(1+(MR²/ε)^{2/5}+δR/ε), with logs from restarts, precision and radius search (my sketch, not checked line by line) → same bound, log-free | Removes logarithms only | None | None | Not verified in the literature as an end-to-end theorem |

**Standard-reduction check.** I found no substitution that yields the δ > 0 residual bound directly. The plausible composition in the last row gives the same rate up to logarithms, a point the companion note also concedes. The new mechanism is the restart-based radius search inside each subproblem. Each phase's cost is tied to the actual root distance r_k, not to the guessed radius. That cost is then summed against the outer anchored energy (Σ a_k r_k ≤ 4λR√K), which is what removes the logarithms. Proof ancestry: Jiang–Yoon supply the outer anchored extra-proximal potential, and Agafonov et al. supply the error model. Neither one gives this budget without that additional accounting.

The note's optimality claim combines two lower bounds. Jiang–Yoon Thm 6.1 gives Ω((MR²/ε)^{2/5}) for deterministic algorithms in growing dimension. Park–Ryu (ICML 2022, Thm 4.6), applied with F = (δ/2)(I − T) and J = 0, gives Ω(δR/ε). I checked only that this reduction is plausible; I did not read the lower-bound proofs, so the bound should be read as optimal *if* both transfers hold.

**Search coverage.** On 2026-11-04 I searched arXiv and the NeurIPS proceedings for second-order and inexact-Jacobian methods for monotone VIs and residuals. I read the theorem summaries of 2609.30212, 2609.23557, 2609.13462v2 (compact X, Õ), 2608.08463 (Õ(ε^{-1/2})), 2609.22481 (gap only) and 2405.15990v2. The full texts were long and I read them only partially. I found no prior residual guarantee with inexact Jacobians, but that is not proof that none exists. Whether Zhang et al.'s log-free method carries over to the full space through a ball X = B(x₀, 2R) is unchecked. Its outputs could lie on the ball's boundary, where the tangent residual does not bound ‖F‖. The citations in the companion note match what I found.

**Conclusion**

**The rate itself is not new; the gains are dropping a logarithm and stating the first end-to-end residual bound with inexact Jacobians.** The strongest baseline is Jiang–Yoon (September 2026). For exact Jacobians on the full space, it already reaches the optimal exponent, but with a logarithmic factor:

| | δ = 0 | δ > 0 |
|---|---|---|
| Jiang–Yoon | (MR²/ε)^{2/5}·log(MR²/ε) | not covered |
| Composition (inferred) | — | Õ((MR²/ε)^{2/5} + δR/ε) |
| This result | (MR²/ε)^{2/5} | (MR²/ε)^{2/5} + δR/ε |

So the proved gain is a log(MR²/ε) factor when δ = 0. When δ > 0, I found no published residual theorem at all. However, a natural combination of Jiang–Yoon's outer loop with Agafonov et al.'s restarted inexact-Jacobian solver plausibly gives the same bound up to logarithms. The result is pathwise and last-iterate, and it needs known M, δ, R. Its constant of 2²² rules out any practical claim.

What remains uncertain: I have not checked that the composition works step by step, or that Zhang et al.'s log-free compact-domain analysis extends to the full space. Either check could shrink the contribution further. The search did not establish that the result is first.

The contribution that can be claimed is a clean, log-free bound for monotone equations with δ-inexact Jacobians, which matches the reported lower bounds. It removes logarithms relative to the best known or composable guarantees. It does not improve the polynomial rate, and it covers no instances beyond what that composition plausibly handles.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
