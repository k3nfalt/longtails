# Novelty assessment: HessianLipschitzPLLowerBound

The [theorem](../../LongTails/Theorems/HessianLipschitzPLLowerBound.lean) proves, on the [high-dimensional setup](../../LongTails/Setups/HighDimensionalHessianLipschitzPL.lean) (which uses the predicates of [HessianLipschitzPL](../../LongTails/Setups/HessianLipschitzPL.lean); hard instance in [HessianPLHardness](../../LongTails/Proofs/HessianPLHardness.lean)), the following. Take any randomized adaptive algorithm that knows all parameters and receives exact (f, ∇f, ∇²f) per query. For every budget b ≤ ⌊(H²Δ/μ³)^{1/4}/2³⁹⌋, there is an H-Hessian-Lipschitz, globally μ-PŁ objective on ℝᵈ with an attained minimum and f(0) − f⋆ ≤ Δ, chosen depending on the algorithm and b but not on its seed. On it, 𝔼[f(X)] − f⋆ > ε (or the integrability clause fails). No `allowedAlgorithm` restriction applies.

**Necessary budget.**

  Ω( √H · Δ^{1/4} · μ^{-3/4} ) joint value/gradient/Hessian calls.

The parameters are: H, the Hessian-Lipschitz constant (operator norm); μ, the PŁ constant in 2μ(f − f⋆) ≤ ‖∇f‖²; Δ, the initial gap; ε, the expected-gap accuracy; d, the dimension. The bound needs ε ≤ Δ/32, H²Δ/μ³ ≥ 2¹⁶⁰ and d ≥ H²Δ/μ³. No gradient-Lipschitz bound and no convexity are assumed. The bound does not depend on ε.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| No previous second-order lower bound for a PŁ or gradient-dominated class was found. Closest: Yue–Fang–Lin, *On the Lower Bound of Minimizing PŁ Functions* ([arXiv:2212.13551](https://arxiv.org/abs/2212.13551), COLT 2023), Thm 3. **First-order oracle, L-smooth PŁ class.** | Ω((L/μ) log(1/ε)) gradient calls for deterministic methods → Ω(√H Δ^{1/4} μ^{-3/4}) value/gradient/Hessian calls for randomized methods | Not comparable: different oracle and class. Their hard function (eqs. 12–17) is piecewise quadratic and not C², so it has no finite H, and it does not transfer. | First-order oracle, L-smooth class → second-order oracle, H-Hessian-Lipschitz class with no L | Deterministic → randomized algorithms | No ε-dependence (their log(1/ε) has no counterpart here). Needs d ≥ H²Δ/μ³. |
| Arjevani–Shamir–Shiff ([arXiv:1705.07260](https://arxiv.org/abs/1705.07260), Math. Program. 2019), Thm 1; Kornowski–Shamir ([arXiv:2010.06642](https://arxiv.org/abs/2010.06642)). **Applies only to the strongly convex subclass**, with distance parametrization D. | Ω((HD/μ)^{2/7} + log log) for deterministic methods. With D² ≤ 2Δ/μ this is at most Ω((H²Δ/μ³)^{1/7} + log log) → Ω((H²Δ/μ³)^{1/4}) | The polynomial exponent improves from 1/7 to 1/4 when H²Δ/μ³ ≥ 2¹⁶⁰. No reduction from this subclass can reach 1/4, because restarted optimal second-order methods solve it in Õ((H²Δ/μ³)^{1/7}) (the companion note's claim; not re-derived). | Strongly convex → PŁ only (nonconvex) | Deterministic → randomized | Loses the log log(1/ε) term. Needs much larger dimension. I did not verify that their hard instances satisfy gap ≤ Δ. |
| Carmon–Duchi–Hinder–Sidford ([arXiv:1710.11606](https://arxiv.org/abs/1710.11606), Math. Program. 2020), Thm 2, p = 2. **Stationarity criterion; the hard functions are not PŁ.** | Ω(Δ√H ε_g^{-3/2}) for ‖∇f‖ ≤ ε_g. Setting ε_g² ≍ μΔ formally gives the same order (H²Δ/μ³)^{1/4} | Not comparable: different class and criterion. The Φ-tails of their chain have gap/‖∇f‖² → ∞, so the chain is not PŁ. | Non-PŁ class → hard instances inside the PŁ class | Gradient norm → objective gap | Carmon et al. need dimension ≈ T² log T rather than ≈ T⁴. |
| Nesterov–Polyak ([doi:10.1007/s10107-006-0706-8](https://doi.org/10.1007/s10107-006-0706-8), 2006), Thm 7, and the repository's [companion upper bound](../../LongTails/Theorems/HessianLipschitzPLCubicNewton.lean) (same setup, by inclusion). **Upper bound, for gap closure.** | O((H²Δ/μ³)^{1/4} + log log(1 + μ³/(H²ε)) + 1) → lower bound Ω((H²Δ/μ³)^{1/4}) | Closes the global polynomial term up to universal constants. The additive log log term is not matched. | None (same class) | Not applicable | The lower bound holds only for ε ≤ Δ/32 and in high dimension. |

**Reduction check and proof ancestry.** None of the standard reductions gives this bound. Strongly convex instances are too easy (exponent ≤ 1/7). Carmon's chain is not PŁ. Yue–Fang–Lin's chain is not C². The new step is to prove that a guarded C³ chain is *globally* PŁ with constant of order 1/N, while unfinished points keep a gap of order N.

The guarded chain is −Φ(y₀) plus gated arctan links, plus (a/2)‖x‖², with a radial cutoff. The PŁ proof uses a bracket decomposition and a case split into saturated and unsaturated points. The proof ancestry is the zero-chain and randomized-hiding paradigm of Carmon et al., together with the repository's existing [RelativeHessianLocalized](../../LongTails/Proofs/RelativeHessianLocalized.lean) chain and its injection-counting argument. Both are reused, with the PŁ lemma added. I read the formal statement and the lemma structure; I did not run the build or the audit.

**Search coverage.** The searches were run on 2026-11-21. They used web search over arXiv, PMLR/COLT, Math. Program. and OpenReview, combining "lower bound" with PŁ, gradient-dominated, Łojasiewicz, second-order, Hessian, cubic Newton and tensor/higher-order. I read Yue–Fang–Lin (ar5iv, first part verbatim) and Masiha–Kiyavash–Thiran ([arXiv:2606.28278](https://arxiv.org/abs/2606.28278), first-order only; v3 Remark 4.6 disclaims the Lipschitz-Hessian class). I also read Table 2 of the Nesterov survey [arXiv:2611.07114](https://arxiv.org/abs/2611.07114), whose second-order lower bounds are convex only.

The arXiv API was unreachable, and I did not re-read the full texts of Nesterov–Polyak, Arjevani–Shamir–Shiff or Kornowski–Shamir in this session. The companion note's citations and claims agree with what I checked. The lower bound was introduced in commit e200c8de (2026-11-21).

**Conclusion**

**Yes: this appears to be the first lower bound for second-order methods on PŁ functions with Lipschitz Hessian, and it matches the global phase of cubic Newton.** The upper bound being matched is Nesterov–Polyak's 2006 analysis of cubic-regularized Newton, made logarithm-free in the companion theorem:

| | Bound (queries) |
|---|---|
| Cubic Newton (upper) | O((H²Δ/μ³)^{1/4} + log log(1 + μ³/(H²ε))) |
| This result (lower, randomized) | Ω((H²Δ/μ³)^{1/4}) for ε ≤ Δ/32, d ≥ H²Δ/μ³ |
| Best transferable prior (strongly convex subclass) | at most Ω((H²Δ/μ³)^{1/7} + log log) |

Strong convexity gives exponent 1/7 at best, which shows that second-order acceleration is impossible under PŁ alone. This is the second-order analogue of Yue–Fang–Lin's first-order separation, and no standard reduction gives it: the known hard chains are either not PŁ or not twice differentiable.

The limits are the missing log log(1/ε) term, the threshold H²Δ/μ³ ≥ 2¹⁶⁰, and the dimension requirement d ≥ H²Δ/μ³. The comparison shows the result is strictly stronger than anything transferable from the checked works. Priority rests on keyword searches and on the papers I could read, so it is not exhaustive.

The claimable contribution is a tight (up to constants) randomized lower bound on the polynomial part of the second-order complexity of globally PŁ, Hessian-Lipschitz minimization.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
