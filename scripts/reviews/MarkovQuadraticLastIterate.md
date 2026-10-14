# Novelty assessment: `MarkovQuadraticLastIterate`

[`result`](../../LongTails/Theorems/MarkovQuadraticLastIterate.lean) proves the following for the setup [`MarkovQuadraticInterpolation`](../../LongTails/Setups/MarkovQuadraticInterpolation.lean). Take finitely many self-adjoint operators 0 ⪯ Hᵢ ⪯ L·I on a complete separable Hilbert space, with f(x) − f(u) = ½ Σᵢ πᵢ⟨x−u, Hᵢ(x−u)⟩. The oracle returns H_{sₜ}(x−u), where sₜ is a finite Markov chain with stationary law π, an arbitrary initial law, and κ(i,·) ≥ α·π. Under these assumptions, the **last iterate** of plain [SGD](../../LongTails/Algorithms/MarkovQuadraticSgd.lean) with η = α/(10⁴L) satisfies 𝔼[f(x_K) − f(u)] ≤ ε.

**Proved complexity.** The budget is K = ⌈10¹⁶·LR²/(αε)⌉ + 1, so

  **O(1 + LR²/(αε))** oracle calls, for L > 0, R ≥ 0, 0 < α ≤ 1 and ε > 0.

Here L bounds the Hessians from above, R ≥ ‖x₀ − u‖, α is the known refresh probability, and ε is the target expected gap. No dimension, state count or curvature lower bound appears. The proof goes through `Model.iterate_risk_bound`, which gives 4.5·10¹⁵·LR²/(αn) for every n ≥ 1. The theorem was introduced in commit 75b5c06 on 2026-09-29.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Averaged SGD with η = 1/L on the **same class**. This is a derived baseline, verified below, not a published theorem. | ⌈LR²/(2αε)⌉ + 1 = O(1 + LR²/(αε)) → O(1 + LR²/(αε)) | None: same order. The selected constant is about 2·10¹⁶ times larger. | None. The baseline does not even need π to be stationary. | Average of x₁,…,x_{K−1} → last iterate of plain SGD. An average is not the last iterate of plain SGD, but under the setup's criterion any output counts. | The selected method needs α inside its step size and uses a step 10⁴/α times smaller. The baseline needs α only for its budget. |
| Thinning (the SGD-DD idea of [Nagaraj et al., NeurIPS 2020, Thm 8](https://proceedings.neurips.cc/paper/2020/hash/c22abfa379f38b5b0411bc11fa9bf92f-Abstract.html)) combined with prior i.i.d. last-iterate SGD ([Dereziński–Dong, arXiv:2606.29593v1, 28 Jun 2026, Thm 3.1, Cor 3.3](https://arxiv.org/html/2606.29593v1)) | ≈ 7·(LR²/(αε))·ln(3.5LR²/ε) = O((1 + LR²/(αε))·log(2 + LR²/ε)) → O(1 + LR²/(αε)) | Removes the log(2 + LR²/ε) factor. With the literal constants, the selected bound is smaller only when ln(3.5LR²/ε) > 1.4·10¹⁵. | None | Thinned last iterate, which discards samples → last iterate using every sample | Both methods need α. |
| [Even, ICML 2023, Thm 5.6 and Cor 5.8](https://proceedings.mlr.press/v202/even23a/even23a.pdf): MC-SGD under interpolation. **Applies only when every Hᵢ ⪰ μI with μ > 0.** | On that overlap: O((L/μ)·log(2 + LR²/ε)), for any sampling order and with no mixing requirement → O(1 + LR²/(αε)) | Not comparable in general. On the overlap, the selected bound is smaller only when μ < αε·log(2 + LR²/ε)/(10¹⁶R²). | Strongly convex components → μ = 0 allowed. This covers singular or infinite-dimensional Hᵢ, such as realizable least squares with Hᵢ = aᵢaᵢᵀ. | None | Requires the refresh condition (α). Even's bound does not depend on the sampling order at all. |

**Averaged baseline derivation.** Let eₜ = xₜ − u and take η = 1/L. Since 0 ⪯ H ⪯ L·I, we have ‖He‖² ≤ L⟨e, He⟩, so ‖e_{t+1}‖² ≤ ‖eₜ‖² − ⟨eₜ, H_{sₜ}eₜ⟩/L. Summing gives Σₜ 𝔼⟨eₜ, H_{sₜ}eₜ⟩ ≤ LR². For t ≥ 1, eₜ is determined by the past, and the conditional law of sₜ is at least α·π. Because every term is nonnegative, 𝔼[⟨eₜ, H_{sₜ}eₜ⟩ | past] ≥ 2α(f(xₜ) − f(u)). Jensen's inequality then gives LR²/(2α(K−1)) for the average. This matches the companion note's claim.

**Thinning derivation.** Write κ = (1 − α)Q + απ. Keep every k-th sample, with k = ⌈2ln(N+1)/α⌉, where N is the number of kept samples. Whenever a refresh occurs inside a gap, the kept state is an independent draw from π. The coupling fails with probability at most N(1−α)^k ≤ 1/(N+1). On failure, the gap is still at most LR²/2, because each step is a contraction. Adding D–D's 3LR²/(N+1) gives a total of at most 3.5LR²/(N+1).

**Reduction check and mechanism.** Neither reduction yields a log-free last-iterate bound for plain Markov SGD. The proof's geometric-block energy argument and source-weighted operator-renewal argument (`MarkovQuadraticRisk`, `MarkovOperatorRenewal`) appear to be the genuinely new step. D–D's positive-contraction bound ‖Φᵀ − Φᵀ⁺¹‖ ≤ 3/(T+1) is proof ancestry: it covers only i.i.d. products and must be redone for Markov blocks. Other work does not apply here:
- Nagaraj et al. and Mou et al. assume a positive-definite covariance or Hurwitz stability.
- The repository's [heavy-tailed Markov setup](../../LongTails/Setups/HeavyTailedMarkovSmoothAndConvex.lean) requires a uniform noise-moment bound σ. That bound fails here, because (Hᵢ − H̄)(x−u) is unbounded in x.

No lower bound for this class was verified.

**Search coverage (2026-10-07).**
- Read at theorem level: D–D 2606.29593; Even (ICML 2023); Nagaraj et al. (NeurIPS 2020, via ar5iv).
- Checked by abstract only: Varre et al. (NeurIPS 2021), Attia et al. 2507.11274, and D–D COLT 2026 (2604.09909). These are i.i.d. results, all superseded by D–D Cor 3.3 on this class.
- Not found: any Markov-sampling last-iterate result without curvature dependence.
- Not verified: Mou et al. 2112.12770 at theorem level, and the literature on Kaczmarz with Markov row selection.

The companion note's citations and its averaging and thinning caveats agree with what I found.

## Conclusion

**No complexity or scope gain over plain averaging; the new part is a log-free last-iterate guarantee for Markov SGD.**

On the identical class, averaged SGD with step 1/L already reaches accuracy ε with the same order of calls. Its constant is far smaller, and it needs α only to set the budget:

| Method | Calls to reach ε |
|---|---|
| Averaged SGD (elementary, derived above) | LR²/(2αε) + 1 |
| Thinned SGD + Dereziński–Dong (last iterate) | ≈ 7·(LR²/(αε))·ln(3.5LR²/ε) |
| This result (last iterate) | 10¹⁶·LR²/(αε) + 1 |

The real addition is the output. The last iterate of plain constant-step SGD, using every Markov sample, gets the O(LR²/(αε)) rate without curvature, reversibility or commutativity assumptions. The best derived alternative for a last iterate costs an extra log(LR²/ε). That gain is asymptotic only: with the proved constants it appears only when ln(LR²/ε) exceeds about 10¹⁵. Strongly convex Markov analyses such as Even (2023) do not cover μ = 0.

The comparison establishes that no total-complexity advantage exists. My search found no prior log-free Markov last-iterate result of this kind, but that does not establish priority. The Markov-Kaczmarz literature remains unchecked. What can be claimed is a new method-specific last-iterate analysis that removes a logarithm relative to thinning, not a better optimization guarantee.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
