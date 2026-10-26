# BFGS with arbitrary Armijo–Wolfe steps on f = h(Ax): novelty assessment

[`result`](../../LongTails/Theorems/LinearPredictorBFGS.lean) proves the following. Take BFGS with B₀ = L·I, any history-dependent Armijo–weak-Wolfe steps, and the last iterate x_K as output. For every f = h∘A with convex L_h-smooth h, L ≥ L_h‖A‖², a minimizer x⋆ with ‖x₀−x⋆‖ ≤ R, and (μ/2)‖A(x−x⋆)‖² ≤ f(x)−f⋆ on {f ≤ f(x₀)}, this run reaches f(x_K) − f⋆ ≤ ε deterministically. The setup ([`LinearPredictorBFGS`](../../LongTails/Setups/LinearPredictorBFGS.lean)) restricts the algorithm to `bfgs c x₀`, and the algorithm is [`method`](../../LongTails/Algorithms/LinearPredictorBFGS.lean) = `bfgs L x₀`.

**Proved budget.** Each call to the line-search oracle returns (α, ∇f(x+αv)):

N = ⌈35 (L_h/μ)^{3/2} (c₁(1−c₂))^{−3/2} √(LR²/ε)⌉ + 1 = O(1 + (L_h/μ)^{3/2}(c₁(1−c₂))^{−3/2}√(LR²/ε)).

The parameters are: L_h, the smoothness of h; μ ≤ L_h, the quadratic-growth constant of h on the image of the sublevel set; 0 < c₁ < c₂ < 1, the Armijo/Wolfe constants; R, the initial distance; and ε, the target accuracy. The count covers BFGS iterations; the cost of finding each Wolfe step is not counted. When v = 0, the oracle returns exactly ∇f(x), so it contains a plain gradient oracle. This rests on the setup's gradient obligation for every (x, v).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nesterov AGD / FISTA with ψ = 0 ([Beck–Teboulle 2009, Thm 4.4](https://doi.org/10.1137/080716542)): problem-class competitor, simulated through v = 0 queries | O(1+√(LR²/ε)) → O(1+(L_h/μ)^{3/2}(c₁(1−c₂))^{−3/2}√(LR²/ε)) | **Worse: uniformly**, by a factor ≳ (35/√2)·γ^{−3/2} > 190 against the √(2LR²/ε) AGD bound, since γ = c₁(1−c₂) < 1/4. For c₁ = 10⁻⁴, c₂ = 0.9 and κ = 1 the factor is ≈ 8·10⁸. | None. AGD needs only convexity and L-smoothness. | None. Both give a deterministic last iterate, and both need L. | Requires the composite structure plus quadratic growth of h. Uses a line-search oracle, which is stronger than gradient access. |
| Ding–Yang–Zhou, [arXiv 2608.16009v1](https://arxiv.org/abs/2608.16009) (17 Aug 2026, unrefereed), Thm 3.1, eq. (11): same method and oracle, prior | LW₀²/(γε), W₀ = sup_{f(x)≤f(x₀)} (f−f⋆)/‖∇f‖. On this class there is **no bound in (L, L_h, μ, R, ε)**. Example: h = ½‖·‖², A = diag(1, δ), x₀ = (R, 0) gives W₀ ≥ R/(2δ) → ∞. → 35γ^{−3/2}√(LR²/ε) + 2 here, since κ = 1. | Uniform bound instead of none on this class; order ε^{−1} → ε^{−1/2}. When their W₀ ≈ R (benign geometry), this result wins only if LR²/ε > 1225κ³/γ. | Bounded sublevel set / W₀ < ∞ → initial distance only. This answers their §4 Q2, and Q1 (f(x_k) → f⋆), **only for this subclass**. | None: same output, and the updates use only L. | Their class is all convex L-smooth f, which is broader. On benign instances their 1/k bound has smaller constants when ε is large. |

**Reduction check and mechanism.** I checked two standard reductions. Restricting to x₀ + range(Aᵀ), which BFGS preserves, turns quadratic growth of h into growth with modulus μσ⁺_min(A)². Linear-rate analyses for strongly convex f ([Jin–Jiang–Mokhtari, NeurIPS 2024](https://arxiv.org/abs/2404.16731)) would therefore depend on cond(A). They need strong convexity, not just growth, and are vacuous for singular A. The equivalence between exact-line-search BFGS and CG covers only exact steps on quadratics. Neither reduction gives this bound. The new ingredient appears to be the exact variable-metric identity V_{i+1} = V_i − ⟨g_i, x_i−x⋆⟩²/⟨g_i, B_i⁻¹g_i⟩ + ⟨y_i, x_{i+1}−x⋆⟩²/⟨y_i, s_i⟩. The composite structure enters only to bound the last term by 2κΔ_{i+1}, and a bootstrap then upgrades 1/k to 1/k². The proof also borrows two ingredients from Ding–Yang–Zhou: the 1/Δ telescoping and the trace/log-det potential (Byrd–Nocedal 1989).

**Search coverage.** On 2026-10-25 I searched arXiv, NeurIPS and Math. Program. for convex and non-strongly-convex BFGS rates, initial-distance rates, and follow-ups to Ding–Yang–Zhou. I read their full text. The Sept 2026 papers arXiv 2609.09686 (nonconvex counterexamples) and 2609.09872 (nonsmooth 1-D) are not relevant. I did not access Powell (1976/1986), Dai's counterexamples, or Byrd–Nocedal–Yuan (1987) in full. The Beck–Teboulle bound is cited from standard knowledge and was not re-read. The companion note matches the Lean statement. It already concedes that the comparison with AGD is missing, but it does not quantify that gap. Git history dates the result to 2026-10-25, two months after Ding–Yang–Zhou.

**Conclusion**

**For the optimization problem, no: accelerated gradient descent is uniformly faster. For BFGS itself, yes: this is a new, accelerated-order guarantee in the initial distance.**

On the full class, AGD needs O(1+√(LR²/ε)) gradient calls, which this oracle can supply. BFGS needs (L_h/μ)^{3/2}(c₁(1−c₂))^{−3/2} times more, and the class must also have the composite quadratic-growth structure. So the result does not improve oracle complexity for this problem class.

The method-specific gain is real. The prior Ding–Yang–Zhou bound for the same BFGS method is O(LW₀²/(γε)), and W₀ can be unbounded on this class for fixed L, L_h, μ, R and ε. Ill-conditioned or singular designs A cause this. The new bound depends only on the initial distance and has the optimal order √(LR²/ε) in L, R and ε. This resolves Ding–Yang–Zhou's open question 2 for linear-predictor objectives, including least squares, but not for general convex f.

These comparisons are established. Priority rests on a two-month window and a search that found no competing result. The classical quadratic-case literature was not fully checked, and the very poor constants (κ³/γ³ in the 1/k² bound) limit its practical significance.

The claimable contribution is the first distance-only rate for BFGS with inexact Wolfe steps on h(Ax) objectives, at accelerated order. It does not improve the complexity of the problem class.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
