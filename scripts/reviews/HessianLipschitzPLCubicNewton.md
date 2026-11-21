# Cubic-regularized Newton on PŁ functions with Lipschitz Hessian: novelty assessment

The [theorem](../../LongTails/Theorems/HessianLipschitzPLCubicNewton.lean) covers every finite-dimensional real inner-product space and every `f` with an `H`-Lipschitz Hessian (operator norm), an attained minimum, gap `f(x₀) − f⋆ ≤ Δ`, and the global PŁ inequality `2μ(f − f⋆) ≤ ‖∇f‖²` ([setup](../../LongTails/Setups/HessianLipschitzPL.lean)). For such `f`, the last iterate of fixed-`H` cubic Newton ([algorithm](../../LongTails/Algorithms/CubicNewtonPL.lean)) reaches `f(x_K) − f⋆ ≤ ε` deterministically. Each step is the exact global minimizer of `⟨g,s⟩ + ½⟨s,∇²f s⟩ + (H/3)‖s‖³` and costs one `(f, ∇f, ∇²f)` oracle call. The budget is `K = ⌈53 (H²Δ/μ³)^{1/4} + 5 log(1 + log(1 + μ³/(H²ε))) + 4⌉`.

**Complexity in the original parameters.** Here `H` is the Hessian-Lipschitz constant, `μ` the PŁ constant, `Δ` the initial gap, and `ε` the target accuracy:

  O( 1 + (H²Δ/μ³)^{1/4} + log(1 + log(1 + μ³/(H²ε))) )   second-order oracle calls,   valid for H, μ, ε > 0 and Δ ≥ 0.

The updates use only `H`. The values `μ`, `Δ` and `ε` enter only the stopping count.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nesterov–Polyak, *Math. Program.* 108 (2006), [doi](https://doi.org/10.1007/s10107-006-0706-8), Thm 7 (gradient-dominated, degree 2, `τ_f = 1/(2μ)`); checked in the [2003 CORE preprint](https://research.dial.uclouvain.be/bitstreams/bae87e54-345e-4d37-98f1-d1cd3c9a9226/download). Covers the full target class with the same method (`M = 2H` in their `M/6` normalization, inside their range `M_k ≤ 2L`), the same exact cubic step, and the same last-iterate output. | Read literally: phase 1 has `k₀ ≤ 1 + (1+δ₀^{1/4}) log δ₀` with `δ₀ = Δ/ω̃ ≈ 2592 H²Δ/μ³`, then an order-4/3 phase. Total: `O((1+(H²Δ/μ³)^{1/4}) log(2+H²Δ/μ³) + log(1+log(1+μ³/(H²ε))))` → `O(1+(H²Δ/μ³)^{1/4} + log(1+log(1+μ³/(H²ε))))` | Removes the `log(2 + H²Δ/μ³)` factor from the global phase. This is a Θ(log(H²Δ/μ³)) speedup when `H²Δ/μ³ ≥ 2` and `(H²Δ/μ³)^{1/4} log(H²Δ/μ³) ≳ log log(μ³/(H²ε))`. Otherwise: same order. | None | None (same method, same parameter knowledge, same last iterate) | None. Both results assume an exact global cubic-subproblem solve, and both need `H`. |
| Chayti–Doikov–Jaggi, *TMLR* 09/2024 ([arXiv 2302.11962v5](https://arxiv.org/abs/2302.11962)), App. F, μ-strongly convex corollary with exact derivatives. **Restricted to strongly convex `f`**, a strict subclass. | `O(t₀ + log log(·))` (argument garbled in the extracted text) with `t₀ = Õ(H^{1/2}Δ^{1/4}/μ^{3/4}) = Õ((H²Δ/μ³)^{1/4})` → same as above | Removes only the logarithms hidden in `Õ`, on the overlap | Strongly convex → PŁ (nonconvex instances, non-isolated minimizers). This scope gain is already in Nesterov–Polyak's Thm 7. | None | None on the overlap |

**Standard-reduction check.** The improvement follows in a few lines from Nesterov–Polyak's one-step inequality (4.17), `δ_k ≥ δ_{k+1} + δ_{k+1}^{3/4}`. While `δ_k ≥ 1`, there are two cases. If `δ_{k+1} ≥ δ_k/16`, concavity of `t^{1/4}` gives `δ_k^{1/4} − δ_{k+1}^{1/4} ≥ δ_{k+1}^{3/4}/(4δ_k^{3/4}) ≥ 1/32`. If not, the fourth root at least halves. So at most `32 δ₀^{1/4} + O(1)` steps are needed, with no `log δ₀` factor. The repository's recursion (fourth root decreasing by 1/16 per step, then `u_{k+3} ≤ u_k^{64/27}`) is this argument plus the paper's own 4/3-order local phase. No new mechanism is involved. Proof ancestry: Nesterov–Polyak's Lemma 7/(4.10) and the cubic-model optimality conditions supply the descent and gradient bounds. The related analyses of Zhou–Wang–Liang (NeurIPS 2018) and Yue–Zhou–So (SIAM J. Optim. 2019) are local or asymptotic and are not baselines here.

**Search coverage (2026-11-21).** I searched arXiv, NeurIPS proceedings and the web for cubic-Newton complexity under PŁ/gradient domination. I read Nesterov–Polyak Thm 7 with its proof, the [Masiha et al. (NeurIPS 2022)](https://arxiv.org/abs/2205.12856) introduction (deterministic case: it cites Nesterov–Polyak and gives only `O(log log(1/ε))`), and Chayti–Doikov–Jaggi App. F. The Springer version of record and Nesterov's 2018 textbook were not accessible. The result was introduced in commit `e200c8de` on 2026-11-21, together with a [repository lower bound](../../LongTails/Theorems/HessianLipschitzPLLowerBound.lean) of order `(H²Δ/μ³)^{1/4}` that I did not audit. The [companion note](../../LongTails/Theorems/HessianLipschitzPLCubicNewton.md) itself attributes the rate to Nesterov–Polyak and claims no contribution. That claim is consistent with the Lean statement and with the sources I checked.

## Conclusion

**No new optimization result: this is Nesterov–Polyak's 2006 cubic-Newton guarantee for PŁ functions, with tighter bookkeeping.** Nesterov–Polyak's Theorem 7 covers the same class, method, oracle and last-iterate output. Read literally, its count carries an extra logarithm in the global phase:

| | Second-order oracle calls |
|---|---|
| Nesterov–Polyak Thm 7 (literal) | `(1+(H²Δ/μ³)^{1/4}) log(2+H²Δ/μ³) + log log(μ³/(H²ε))` |
| This theorem | `1 + (H²Δ/μ³)^{1/4} + log log(μ³/(H²ε))` |

The `log(H²Δ/μ³)` saving is real when `H²Δ/μ³` is large. However, it follows from the paper's own inequality (4.17) by a short concavity argument, so it is a routine corollary rather than a new analysis. Strongly convex specializations, such as Chayti–Doikov–Jaggi (TMLR 2024), give the same leading term up to hidden logarithms. Nothing is gained in scope, oracle access, adaptivity (the updates still need `H`), or output type.

What is established is an explicit-constant, fully counted Lean formalization of a known bound with the global-phase logarithm removed. Its value is that it pairs with the repository's lower bound, which this review did not examine. Priority for the log-free statement is not decisive, because I could not access Nesterov's textbook. Even if no earlier source writes the log-free count out, it would still be a standard corollary.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
