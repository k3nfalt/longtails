# Novelty assessment: LazyQuarticHessianTradeoff

[`result`](../../LongTails/Theorems/LazyQuarticHessianTradeoff.lean) proves the following for every C³ function on a finite-dimensional real Hilbert space whose third derivative is L₃-Lipschitz, with `f(x₀) − inf f ≤ Δ` and `‖∇²f(x₀)‖ ≤ H₀`: the deterministic [lazy-Hessian quartic-metric algorithm](../../LongTails/Algorithms/LazyQuarticMetric.lean) uses exact (value, gradient) and full-Hessian oracles and outputs a point with `‖∇f(x_out)‖ ≤ ε` for every seed ([setup](../../LongTails/Setups/ThirdDerivativeSmoothNonconvex.lean)). No global bound on the gradient Lipschitz constant (L₁) or the Hessian Lipschitz constant (L₂) is assumed, and the bound does not depend on the dimension d.

**Proved budget.** The algorithm knows L₃, Δ, H₀ and ε. A full Hessian costs m ≥ 1 value/gradient calls. The theorem's budgets give

```
gradient calls  G = O((1 + Δ^{5/4} L₃^{5/12} ε^{-5/3}) · log(2 + H₀Δ/ε² + L₃Δ³/ε⁴))
Hessian calls   H = O(1 + Δ^{3/4} L₃^{1/4} ε^{-1})
```

The constants are 2⁹⁰ and 2⁶². Below, S := ΔL₃^{1/3}ε^{-4/3}, so G ≈ S^{5/4}log Γ and H ≈ S^{3/4}. Also β := √(L₃Δ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Doikov–Grapiglia, [arXiv:2510.07992v1](https://arxiv.org/abs/2510.07992) (9 Oct 2025; journal version reported in Math. Program. 2026, not checked), Thm 3.5 and Cor 3.6, p=3. **Direct competitor: same class** | Prior: O(d^{1/3}ΔL₃^{1/3}ε^{-4/3} + d) calls, each returning a gradient and a Hessian; weighted cost m(d^{1/3}S + d). This result: S^{5/4}log Γ + mS^{3/4} | Always uses fewer Hessians when S ≥ 1: S^{3/4} versus d^{1/3}S + d. Weighted cost is lower when m·d^{1/3} ≫ S^{1/4}log Γ. Example: m = d, H₀ ≤ β, constants and logs ignored: d^{4/3}S + d² → S^{5/4}log S + dS^{3/4} | None (same pure-L₃ class) | Prior cost depends on dimension; this one is dimension-free. Output: the same ε-stationarity guarantee | Uses about S^{1/4}log Γ/d^{1/3} times more gradients. It is worse when m is small and d is small (e.g. m = d = 1: S → S^{5/4}log). Doikov–Grapiglia adapt to unknown L₃; this method needs L₃, Δ, H₀ |
| Hinder, [COLT 2018 / arXiv:1805.08370v2](https://arxiv.org/abs/1805.08370), Thm 1 and its first-order variant after (8). **Requires global L₁; Lemma 5 needs L₁ only on balls, so localizing it is plausible but unverified** | Prior: O(d·S·log(L₁³/(L₃ε²))) gradient calls → S^{5/4}log Γ + mS^{3/4} | Gain when d ≫ S^{1/4} and m ≪ dS^{1/4} (up to logs) | Global L₁ → only H₀ at x₀, which enters through a logarithm | Prior cost depends on dimension; this one is dimension-free | Needs a Hessian oracle; worse when d ≲ S^{1/4} |
| Carmon–Duchi–Hinder–Sidford, [ICML 2017](https://proceedings.mlr.press/v70/carmon17a.html), Thm 2. **Requires global L₁** | Prior: O(ΔL₁^{1/2}L₃^{1/6}ε^{-5/3}log(L₁Δ/ε²)) = S^{5/4}√(L₁/β)·log gradient calls → S^{5/4}log Γ + mS^{3/4} | √L₁ is replaced by (L₃Δ)^{1/4}. Weighted gain when L₁ ≫ √(L₃Δ) (up to logs) and m ≪ Δ^{1/4}L₁^{1/2}L₃^{-1/12}ε^{-2/3} | Global L₁ → none. New coverage includes quartic least squares Σ((aᵢᵀx)² − bᵢ)², whose Hessian is unbounded | None | Needs Hessians and H₀; worse when L₁ ≲ √(L₃Δ) |

**Reduction check and proof ancestry.** I found no standard reduction that yields this bound.
- Running Carmon et al. on the original problem pays at least √(‖∇²f(x₀)‖/β) polynomially.
- Cubic regularization and its lazy versions ([Doikov–Chayti–Jaggi, ICML 2023](https://proceedings.mlr.press/v202/doikov23a.html); [Chen–Liu–Luo–Zhang, COLT 2026](https://arxiv.org/abs/2501.17488), Thm 4.1) need a global Lipschitz Hessian. In this class the Hessian Lipschitz constant can grow without bound along valleys, for example (y − x²)².
- Chen et al.'s conclusion lists third-order smoothness as future work.
- The new step is a relative third-derivative bound. It controls D³f in the metric ∇²f(s) + 8βI, so the effective smoothness of the whitened problem is β. A movement potential then pays for Hessian refreshes.
- Proof ancestry: Carmon's "guilty" AGD, Hinder/Carmon negative-curvature exploitation, and lazy-Hessian reuse supply ingredients. None of them supplies this bound.

**Search coverage.** I searched on 18 Oct 2026 UTC: arXiv 2025–2026; COLT, ICML and NeurIPS proceedings; lower-order tensor methods; lazy Hessians; and gradient–Hessian tradeoffs.
- [Wu et al., arXiv:2610.22208](https://arxiv.org/abs/2610.22208) (15 Oct 2026) and Chen et al. study tradeoffs in the Lipschitz-Hessian class, not the L₃ class.
- [Zhou, arXiv:2606.05438](https://arxiv.org/abs/2606.05438) proves an ε^{-5/3} lower bound for first-order methods only. It says nothing about algorithms with Hessian access.
- I did not verify any Hessian-count lower bound for this class.
- The theorem was introduced in commit c8636d6 (18 Oct 2026). All cited works predate it.
- The companion note's comparisons agree with the Lean statement. Its Doikov–Grapiglia theorem numbers refer to the journal version, which I did not check.

## Conclusion

**Yes. In the pure third-derivative-Lipschitz class, the proved gradient/Hessian tradeoff is new and beats the strongest applicable method in explicit regimes, but not uniformly.**

The strongest direct competitor is Doikov–Grapiglia's lower-order tensor method. It covers the same class and makes O(d^{1/3}S + d) combined gradient-and-Hessian calls. With a Hessian costing m gradients and logarithms ignored:

| | gradient calls | Hessian calls |
|---|---|---|
| Doikov–Grapiglia | d^{1/3}S + d | d^{1/3}S + d |
| this result | S^{5/4} | S^{3/4} |

Here S = ΔL₃^{1/3}ε^{-4/3}. The new bound is dimension-free and always uses fewer Hessians, with Hessian calls scaling as ε^{-1}. Total cost improves when m·d^{1/3} ≫ S^{1/4}log Γ. It loses when Hessians are cheap and the dimension is small. It also requires knowing L₃, Δ and H₀, whereas Doikov–Grapiglia adapt to L₃.

Within the overlap where the gradient is globally L₁-Lipschitz, the result effectively replaces Carmon et al.'s √L₁ by (L₃Δ)^{1/4} in exchange for Hessian calls. Where the two analyses use the same ingredients, the gains are polynomial. The mechanism that controls the third derivative in the whitened Hessian metric is not a routine substitution.

The comparison establishes this gain. Separately, the literature search found no earlier dimension-free bound with ε^{-1} Hessian calls for this class, but that does not prove priority. Optimality is open, and the constants make the result purely theoretical. What can be claimed is a new joint oracle-complexity tradeoff that improves on the checked baselines in high dimension when Hessians are expensive.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
