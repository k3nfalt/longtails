# Novelty assessment: CohypomonotoneNewtonAcceleration

[`result`](../../LongTails/Theorems/CohypomonotoneNewtonAcceleration.lean) covers every continuously differentiable, globally ρ-cohypomonotone map `F` on a finite-dimensional Hilbert space whose Jacobian is H-Lipschitz and which has a root within distance R of `x₀`. With exact `(F(x), DF(x))` queries ([setup](../../LongTails/Setups/CohypomonotoneNewton.lean)), the stopped output of the [algorithm](../../LongTails/Algorithms/CohypomonotoneNewton.lean) satisfies `‖F(output)‖ ≤ ε` for every seed. The theorem assumes no global Lipschitz bound on `F` and puts no restriction on ρ.

**Budget.** Here H is the Jacobian-Lipschitz constant, ρ ≥ 0 the cohypomonotonicity parameter, R the initial distance to a root, and ε the residual target. Counting value+Jacobian calls (initialization and rejected search trials included), the proved budget is

  N = O( [ (1+ρHR)² + (1+HR²/ε)^{2/5} ] · (1+log(2+ρHR+HR²/ε))² ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jiang–Yoon, [arXiv:2609.30212v1](https://arxiv.org/abs/2609.30212v1) (24 Sep 2026, preprint, prior), Thms 4.4 and 4.6. **Applies only when ρ = 0** (monotone case). | O((HR²/ε)^{2/5}(1+log(1+HR²/ε))) value+Jacobian calls → O((1+(HR²/ε)^{2/5})(1+log(2+HR²/ε))²) | Worse by one log at ρ=0. Thm 6.1 gives the lower bound Ω((HR²/ε)^{2/5}) for monotone `F`, so the Q^{2/5} term is optimal up to logs. | monotone → ρ-cohypomonotone for every ρ ≥ 0 | None (both give a stopped residual) | Extra log². Their method also handles composite inclusions; this one is unconstrained only. |
| Lee–Kim, FEG, [NeurIPS 2021, arXiv:2106.02326](https://arxiv.org/abs/2106.02326), Thm 4.1. **Applies only when F is L-Lipschitz and ρ < 1/(2L).** | O(LR/((1−2ρL)ε)) value calls → N Jacobian calls | Not comparable in cost units. In call counts, N is smaller when LR/ε ≫ (HR²/ε)^{2/5} + (ρHR)², up to logs (e.g. L=H=R=1, ρ=1/4: ε⁻¹ → ε^{-2/5}). | global L-Lipschitz and ρL<1/2 → no Lipschitz bound on F, any ρ | None | Needs an H-Lipschitz Jacobian and full-Jacobian queries. FEG needs only values and no H. |
| Repo [AdjointAcceleratedCohypomonotone](../../LongTails/Theorems/AdjointAcceleratedCohypomonotone.lean) (added 14 Oct 2026, prior). **Applies only when F is L-Lipschitz.** | O((1+ρL+LR/ε)log(2+ρL) + (1+ρL)⁵ log(2+ρL)·(HR/L)·log²(2+LR/ε)) value + vector–Jacobian-product calls → N | Mixed. Gain at L=H=R=ρ=1: Õ(ε⁻¹) → Õ(ε^{-2/5}). Loss at L=R=ρ=1, H=M, ε=1/M with M→∞: Õ(M) → Õ(M²). | global L-Lipschitz → none | None | Needs full Jacobians instead of vector–Jacobian products. Loses when (ρHR)² ≫ LR/ε + (1+ρL)⁵HR/L. |

**Reductions.** Combettes–Pennanen's transformation (Lemma 2.4) makes G = F∘(I+γF)⁻¹ monotone. Applying Jiang–Yoon to G still needs a robustness analysis for inexact inverse evaluations, plus a starting point whose distance does not depend on ‖F(x₀)‖. Neither is in the cited sources. The companion note's composed bound Õ(q²+qQ^{2/5}), with q = 1+2ρHR and Q = HR²/ε, is a reconstruction, not a published guarantee. The new mechanism is charging inversion work additively, using warm-started bracketing, a robust merit test, a perturbed energy inequality, and a trust-region initializer. Proof ancestry: Jiang–Yoon supply the acceleration framework and the 2/5 exponent; Polyak–Tremba supply the damped-Newton primitive; [arXiv:2609.13462v2](https://arxiv.org/abs/2609.13462v2) (monotone, bounded domain) is a close precedent for amortizing inner-solver cost.

**Example check.** I checked the note's example F(x) = ∇(1+‖x‖²)^{3/2} − mx + 4mJx, with J orthogonal skew and m > 3. Its Hessian part grows linearly, so F has no global Lipschitz constant, while the Jacobian is Lipschitz. The averaged-Hessian argument gives ‖F(x)−F(y)‖ ≥ m‖x−y‖ and ρ = 1/m. F is nonmonotone at 0. None of the baselines above covers it.

**Search coverage.** On 2026-10-27 UTC I searched arXiv, NeurIPS/ICML pages and Google-indexed sources for second-order, Newton and tensor methods for comonotone, cohypomonotone and weak-Minty problems. Besides the papers above, I checked [arXiv:2609.23557](https://arxiv.org/abs/2609.23557) (monotone only) and [Vyas–Bullins, arXiv:2603.13491](https://arxiv.org/abs/2603.13491). Vyas–Bullins Thm 3.3 uses a different s-th-order weak-MVI condition ⟨F(z),z−z*⟩ ≥ −(ρ/2)‖F‖^{3/2}, requires ρ to be small relative to L₂, and gives a best-iterate O(ε⁻²) rate, so it is not a competitor. I found no end-to-end second-order guarantee for cohypomonotone equations. I read the theorem statements cited above; Alacaoglu–Kim–Wright (ρ<1/L, globally Lipschitz `F`) was checked only from its abstract. The note's claims match the Lean statement.

**Conclusion**

**Yes: it extends the optimal monotone second-order residual rate to cohypomonotone equations with any ρ, and the cost of nonmonotonicity is additive.** The closest end-to-end baseline is Jiang–Yoon's monotone method, which this result matches up to one log at ρ = 0:

  monotone (Jiang–Yoon): Õ((HR²/ε)^{2/5})  →  ρ-cohypomonotone (this result): Õ((1+ρHR)² + (HR²/ε)^{2/5}).

Every other checked guarantee for cohypomonotone root-finding assumes a globally Lipschitz `F`. The first-order ones also need ρL < 1, and the repository's adjoint method costs Õ(LR/ε) or more. This theorem drops the global Lipschitz bound and the ρL restriction, at the price of a Lipschitz Jacobian and full-Jacobian queries. The note's example shows that nonmonotone maps with unbounded Jacobians are covered. On the overlap with globally Lipschitz `F`, it improves the leading accuracy exponent from 1 to 2/5 when ρHR is moderate. It loses when (ρHR)² dominates LR/ε.

The comparison establishes this scope gain and the regime-specific gain. Priority rests on a search of a fast-moving area with many September–October 2026 preprints. The search found no published second-order cohypomonotone method, and simply composing known results leaves the inexact-inversion step unproved. Optimality of the (1+ρHR)² term is open.

What can be claimed: the first checked accelerated second-order residual guarantee for globally cohypomonotone equations without operator-Lipschitz or ρ restrictions, whose inversion overhead is additive.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
