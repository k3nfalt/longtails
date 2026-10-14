# Local Nesterov acceleration under strong aiming toward a curved minimizer set

[`result`](../../LongTails/Theorems/LocalStrongAimingNesterov.lean) proves the following. Take ordinary fixed-parameter Nesterov with η = 1/(4L), β = (1−q)/(1+q), q = √(μη), v₀ = 0 and no restarts ([algorithm](../../LongTails/Algorithms/NearestAimingNesterov.lean)). Its last iterate satisfies f(x_K) − f* ≤ ε. This holds for every globally differentiable f on a finite-dimensional Euclidean space that attains its minimum and satisfies three conditions on the tube U_r = {d(x,M) < r} around M = argmin f: an L-Lipschitz gradient, two-point weak convexity with constant √(μL), and μ-strong aiming toward every nearest minimizer. The initialization must satisfy x₀ ∈ U_r and f(x₀) − f* ≤ Δ ≤ μr²/256 ([setup](../../LongTails/Setups/LocalStrongAiming.lean)).

**Complexity.** The proof gives f(x_K) − f* ≤ 2Δ(1 − ½√(μ/L))^K. The theorem uses exactly

  K = ⌈2√(L/μ)·log(1 + 2Δ/ε)⌉ = O(√(L/μ)·log(1 + Δ/ε)) exact gradient calls,

where L is the tube smoothness constant, μ is the strong-aiming constant, Δ is the initial gap, and ε > 0 is the target accuracy. The domain is 0 ≤ Δ ≤ μr²/256 with x₀ ∈ U_r. Updates need only L, μ and x₀. The horizon also needs Δ and ε, and there is no stopping certificate.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gupta–Wojtowytsch, [ICLR 2025, arXiv:2410.08395v3](https://arxiv.org/abs/2410.08395v3), Thm 11 (prior; same NAG scheme). **Restriction:** the nearest-point projection is affine, so M is an affine subspace. | With η = 1/L, the bound is (1−√(μ/L))ⁿ[Δ + (μ/2)d(x₀,M)²]. Strong aiming gives quadratic growth, so this is O(√(L/μ)·log(1+Δ/ε)) → O(√(L/μ)·log(1+Δ/ε)) | None: same order (the contraction constant is 1 vs ½) | Affine M → any closed M, locally. This newly covers curved minimizer sets, such as graphs of C^{1,1} maps; the conditions are needed only on a tube. The two classes are incomparable. | None: same information and the same last-iterate gap | Local only: needs Δ ≤ μr²/256 and x₀ ∈ U_r, while Thm 11 is global. Weak-convexity thresholds are similar (√(μL) here vs. √(μL)/2 there). |
| Hermant–Aujol–Dossal–Huang–Rondepierre, [arXiv:2512.16533v2](https://arxiv.org/abs/2512.16533v2) (Jan 2026 preprint; prior), Thm 20 / Cor 23. **Restriction:** convex M with C² boundary. | Randomized continuized NAG. The rate is ≈ √(μ/L), either for E[e^{ηT_k}(f−f*)] or with constant probability. Requires μ/L < ≈0.15. → deterministic O(√(L/μ)·log(1+Δ/ε)) | Not comparable: different (randomized) output criterion | Convex M → nonconvex, curved M. The classes are incomparable: their theorem needs no weak-convexity bound. | Expectation/high-probability → deterministic bound for the last iterate | Ours is local and needs weak convexity. Theirs is global with convex M only. |
| Feng–Yuan, [arXiv:2603.21516v1](https://arxiv.org/abs/2603.21516v1) (23 Mar 2026 preprint; prior), Thm 2.2. **Restriction:** C² objectives satisfying a local PL condition. | Only an asymptotic rate is proved: ‖x_n − x′‖ ≤ C_ε·(…)·(1 − 2√μ/√(3L+μ) + ε)ⁿ on an unspecified neighbourhood U. The constant C_ε and U are not explicit, so no call bound in (L,μ,Δ,ε) follows → O(√(L/μ)·log(1+Δ/ε)) | Not comparable: the prior result has no explicit budget. Its asymptotic contraction constant is better (2/√3 vs ½). | Requires C² → no C² requirement. This covers the instances verified below: f is not C² and the projection is non-differentiable. Restricted to C² objectives, our hypotheses (strong aiming plus weak convexity) are stronger than PL. | Asymptotic rate with an implicit basin → explicit nonasymptotic bound with explicit basin Δ ≤ μr²/256 | Stronger aiming and weak-convexity hypotheses. Worse rate constant. |

**Reductions and mechanism.** The result does not follow by rescaling or by composing the theorems above. Thm 11 relies on a constant projector P. Hermant et al. use the 1-Lipschitz projection onto a convex set. Feng–Yuan linearize at x* with nonexplicit constants. The new step is an energy built from the convex Asplund-type function ½(‖z‖² − d(z,M)²). Its Bregman divergence exactly absorbs the drift of the footpoint; this replaces both the projection-sign argument and the tangent-space approximation. Proof ancestry is the G–W Lyapunov function and the moving-projection distance energies of Aujol et al. ([arXiv:2403.06930](https://arxiv.org/abs/2403.06930)). Kassing–Weissmann ([arXiv:2410.16849](https://arxiv.org/abs/2410.16849)) prove a local asymptotic rate for heavy ball under local PL. Their result requires C⁴ objectives and also gives no explicit budget.

**Example check.** I checked the note's example f(u,v) = (a/2)(v − ψ(u))², with ψ = bσ and σ(t) = t₊²/(1+t₊²). Using d ≤ |r| ≤ Dd and a Taylor bound for ψ, it satisfies strong aiming with μ = m/2, weak convexity with constant ≤ m/8, and the stated L on the tube r₀ = m/(4HBD). Here M is a curved graph and f is not C². Nearest points are unique on this tube, so the verified example shows a non-differentiable projection, not a non-unique one.

**Search coverage.** On 2026-10-07 I checked arXiv versions of G–W (v3, which still lists the non-affine case as future work, §4), Hermant 2602.10022v2 (aiming toward a fixed minimizer; randomized; rate a(μ₀/L₀)^{1/4}√(μ/L)), Hermant et al., Feng–Yuan and Kassing–Weissmann, and ran targeted web searches. The result was introduced in commit d447752 on 2026-09-30, after all of these sources. I could not locate a manuscript by Obreiter–Steinbrecher–Förster, and NeurIPS 2026 proceedings were not checked. The companion note's citations match the sources. Its phrase "uniqueness of projection is not assumed" is accurate as a hypothesis statement, but I did not verify instances with non-unique projections.

## Conclusion

**The rate is unchanged; the gain is a broader setting with an explicit local basin for ordinary Nesterov.**

The strongest direct baseline is Gupta–Wojtowytsch Thm 11. It gives the same order, but only when the minimizer set is affine:

  G–W: O(√(L/μ)·log(1+Δ/ε)) (affine M, global)  →  here: O(√(L/μ)·log(1+Δ/ε)) (any closed M, local, Δ ≤ μr²/256).

The verified example is a non-C² objective whose minimizer set is a curved graph. It shows that the new class contains instances that no checked prior non-asymptotic theorem covers.

Feng–Yuan (C², local PL) already prove asymptotic local acceleration of NAG around curved minimizer sets, with a better contraction constant. Their neighbourhood and constant C_ε are implicit, however, so they give no oracle budget. The present theorem adds an explicit basin and budget, and it drops the C² requirement. In exchange, it needs strong aiming and tube weak convexity rather than PL, and it is only local.

This comparison establishes a scope and explicitness gain, not a faster rate. My search found no earlier result of this kind, but that does not prove priority. What can be claimed is the first checked explicit, nonasymptotic √(L/μ)-type complexity bound for fixed-parameter NAG near nonconvex minimizer sets without C² or projection-regularity assumptions, proved by a new exact-divergence energy argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
