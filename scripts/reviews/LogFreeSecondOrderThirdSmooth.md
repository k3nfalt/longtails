# Novelty assessment: LogFreeSecondOrderThirdSmooth

[`result`](../../LongTails/Theorems/LogFreeSecondOrderThirdSmooth.lean) shows the following for every C³ function on a finite-dimensional real Hilbert space whose third derivative is globally L₃-Lipschitz, with f(x₀) − inf f ≤ Δ and ‖∇²f(x₀)‖ ≤ H₀ ([setup](../../LongTails/Setups/ThirdDerivativeSmoothNonconvex.lean)). The proximal-Newton method [`LogFreeProxNewton`](../../LongTails/Algorithms/LogFreeProxNewton.lean) uses exact (f, ∇f) and ∇²f oracles and outputs a point with ‖∇f‖ ≤ ε for every seed. The method needs no global Lipschitz gradient or Hessian, and the bound has no dimension factor.

**Complexity.** The proof requires L₃, Δ, ε > 0 and H₀ ≥ 0. Each channel's budget is ⌈2³⁰(1 + S + log Γ)⌉, where S = ΔL₃^{1/3}ε^{-4/3} and Γ = 2 + H₀Δ/ε² + S³. Because log(S³) ≤ 3S, this reduces to

  **O(1 + ΔL₃^{1/3}ε^{-4/3} + log(2 + H₀Δ/ε²))** (f,∇f) calls, and the same number of Hessian calls.

The update rules use only L₃ and ε. Δ and H₀ enter only through the step count.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| He–Zhang, [arXiv:2610.36256v1](https://arxiv.org/abs/2610.36256) (26 Oct 2026, unreviewed; prior by 12 days), Thm 4.7 with ε_H = 2(L₃ε²)^{1/3} | O(S·[1 + log(1 + L_H/(L₃²ε)^{1/3})]) second-order evaluations → O(1 + S + log(2 + H₀Δ/ε²)) | Removes a multiplicative log. This gains when L_H ≫ (L₃²ε)^{1/3} and S ≳ log(2 + H₀Δ/ε²); at fixed constants and ε → 0 the factor is about ⅓·log(1/ε). **Worse** when S·log(1 + L_H/(L₃²ε)^{1/3}) ≪ log(2 + H₀Δ/ε²). | Global L_H-Lipschitz Hessian + L₃ → L₃ only. Localizing their L_H, which enters only inside a logarithm, looks plausible but is unchecked. | None. Theirs is the stronger output. | Loses their (ε_g, ε_H) second-order stationarity and the adaptive-L variant (their Thm 5.6). Adds an H₀ dependence. |
| Doikov–Grapiglia, [arXiv:2510.07992](https://arxiv.org/abs/2510.07992) (Math. Program. 2026), p = 3 result ([repo review](../../LongTails/Theorems/LazyQuarticHessianTradeoff.md)) | O(d^{1/3}S + d) second-order calls → O(1 + S + log(2 + H₀Δ/ε²)) | Factor d^{1/3} on S, and the additive d becomes log(2 + H₀Δ/ε²). Gains unless H₀Δ/ε² ≳ e^{d^{1/3}S + d}. | None: same class | None | Requires H₀, which DG does not. DG's d-dependence was taken from the repository's check, not re-read. |
| AR₃ tensor method, Birgin et al., Math. Program. 163 (2017) | O(1 + S) with third-order oracle and quartic-model minimization → O(1 + S + log(2 + H₀Δ/ε²)) | None: same order in S. Not comparable on oracle. | None | None | This result is weaker in oracle access: no third derivatives or tensor subproblems. That is the advantage. |
| Repo [LazyQuarticHessianTradeoff](../../LongTails/Theorems/LazyQuarticHessianTradeoff.lean), same setup | O((1 + S^{5/4})log Γ) gradients + O(1 + S^{3/4}) Hessians → O(1 + S + log Γ) of each | Fewer gradients. **Worse** on Hessians (S versus S^{3/4}). | None | None | Neither dominates when Hessians are expensive. |

**Reduction check and mechanism.** Plugging this setup into He–Zhang is not enough. A localized L_H, bounded by H₀, L₃, Δ and a path-length bound, still leaves S·log(poly) because their inner Newton loop has length log₄(1 + L_Hμ/(L₃ε)). So the log removal is not a substitution or a known reduction. The new mechanism combines tests of consecutive Hessians against summable thresholds, an escape along the Newton direction whose gain grows like 2^j with the tail level, and an amortized potential that charges log Γ only to the final tail. Proximal-point Newton steps and the Carmon et al. [lower bound](https://arxiv.org/abs/1710.11606) (Ω(S) for any-order randomized algorithms in high dimension; I did not re-verify the theorem number) are proof ancestry and the optimality reference, not baselines.

**Search coverage.** On 7 Nov 2026 UTC I searched arXiv and the web for second-order or tensor methods under third-order smoothness and lazy/secant tensor approaches, and read He–Zhang v1 (Thms 4.7 and 5.6, Concluding Remarks) through HTML. Their concluding-remarks wording on removing the logarithm is paraphrased and not verified verbatim. I did not find the Cartis et al. (2025) lazy-tensor paper that He–Zhang cite (reported O(d·…)). The companion note matches the Lean statement; its "first dimension-free O(S) + O(log Γ) second-order method" claim is consistent with this search but not established by it. I did not run the build or the comparator.

## Conclusion

**Yes, but the gain is one logarithmic factor, and only for first-order stationarity.** The strongest baseline is He–Zhang's proximal-point Newton method (posted 12 days earlier). It already gives a dimension-free O(ΔL₃^{1/3}ε^{-4/3}) rate with second-order oracles, up to a logarithm, and it also guarantees approximate second-order stationarity.

| | Calls for ‖∇f‖ ≤ ε |
|---|---|
| He–Zhang (needs global L_H) | S·(1 + log(1 + L_H/(L₃²ε)^{1/3})) |
| This result (L₃ only) | 1 + S + log(2 + H₀Δ/ε²) |

When L_H ≫ (L₃²ε)^{1/3} and S dominates log(H₀Δ/ε²), this matches the any-order lower bound Ω(S) up to a universal constant, whereas He–Zhang lose a log(1/ε)-type factor. It loses when S is small and H₀ is huge. It also gives up their second-order stationarity guarantee and their adaptive variant. Dropping their global Lipschitz-Hessian assumption may well be a routine localization.

The comparison proves a real logarithmic gain with a new amortized escape mechanism. The literature search supports priority but is only 12 days ahead of an unreviewed competitor. What can be claimed is a log-free, Hessian-Lipschitz-free, optimal-order first-order-stationarity bound for second-order methods under third-order smoothness. That is a modest improvement over He–Zhang, limited to a logarithmic factor and a weaker output criterion.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
