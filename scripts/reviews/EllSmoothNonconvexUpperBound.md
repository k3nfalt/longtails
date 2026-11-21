# Gradient descent under ℓ-smoothness (nonconvex): novelty assessment

[`EllSmoothNonconvexUpperBound.result`](../../LongTails/Theorems/EllSmoothNonconvexUpperBound.lean) proves the following. Take any f : ℝᵈ → ℝ with a differentiable gradient, ‖D∇f(x)‖ ≤ ℓ(‖∇f(x)‖) and f(x⁰) − inf f ≤ Δ, where ℓ is nondecreasing, positive on (0,∞), and has ℓ(u)/u^ρ nonincreasing for some ρ ∈ [0,2] ([setup](../../LongTails/Setups/EllSmoothNonconvex.lean)). Then the frozen gradient method [`ellGd`](../../LongTails/Algorithms/EllSmoothGd.lean) returns a last iterate with ‖∇f(x̂)‖ ≤ ε deterministically, after ⌊16Δℓ(ε)/ε²⌋ + 1 exact gradient calls. The method steps x ← x − g/(2ℓ(2‖g‖)) and stops moving once ‖g‖ ≤ ε.

**Complexity:** O(1 + Δ ℓ(ε)/ε²) gradient calls. Here Δ bounds the initial gap, ε is the target gradient norm and ℓ is the smoothness profile. For ℓ(u) = L₀ + L_ρu^ρ this is O(1 + L₀Δ/ε² + L_ρΔ/ε^{2−ρ}).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2412.11773](https://arxiv.org/abs/2412.11773) v2 (27 Jun 2025), [ICML 2025](https://icml.cc/virtual/2025/poster/44126), Thm 5.1 (direct competitor, prior) | Thm 5.1 gives min_{k<T} ‖∇f_k‖²/ℓ(2‖∇f_k‖) ≤ 4Δ/T. If every ‖∇f_k‖ > ε, regularity gives ℓ(2u) ≤ 4ℓ(ε)u²/ε², so T < 16Δℓ(ε)/ε². That is ⌊16Δℓ(ε)/ε²⌋+1 → ⌊16Δℓ(ε)/ε²⌋+1 | None: the bound is identical, constant included | Minor technical extensions. Locally Lipschitz ℓ with ℓ(0) > 0 → monotone ℓ, possibly with ℓ(0) = 0. Twice-differentiable f → differentiable ∇f (essentially the same). The case ℓ(0) = 0 reduces to ℓ+δ, because the budget inequality is strict. I did not check whether Tyurin's proof needs continuity of ℓ | Best iterate → frozen last iterate. This is a trivial conversion, since ‖∇f‖ is observed at every step | Narrower in ℓ: it requires the order-ρ regularity with ρ ≤ 2 that Tyurin's theorem does not need (his Thm 5.1 and Cor. 5.2 cover general ℓ). Closed-form step instead of an integral step |
| Vankov et al., [arXiv:2410.10800](https://arxiv.org/abs/2410.10800) v3, Thm 3.1 (special case ρ = 1 only, prior) | 2L₀Δ/ε² + 3L₁Δ/ε → 16(L₀Δ/ε² + L₁Δ/ε) | Worse: constants 8× and ≈5.3× larger | Covers ρ ≠ 1 (but Tyurin already does) | Min-iterate → last iterate (trivial, as above) | None beyond constants |
| Li et al., [arXiv:2306.01264](https://arxiv.org/abs/2306.01264) (NeurIPS 2023), Thm 5.2 (sub-quadratic ℓ, older) | O(Δℓ(2G)/ε²), where G = sup{u : u² ≤ 2Δℓ(2u)} → O(Δℓ(ε)/ε²) | Better whenever ℓ(2G) ≫ ℓ(ε). For polynomial ℓ this holds once L_ρ(ΔL_ρ)^{ρ/(2−ρ)} ≫ L₀ + L_ρε^ρ. The gain was already obtained by Tyurin | Sub-quadratic ℓ → ρ = 2 allowed (also already covered by Tyurin) | None | None |

Within the repository, [GdNonconvex](../../LongTails/Theorems/GdNonconvex.lean) gives ⌈2LΔ/ε²⌉ for L-smooth f. The ρ = 0 case here gives 16LΔ/ε², which is the same order with a worse constant.

**Reduction check and proof ancestry:** the bound is exactly a substitution of the regularity inequality into Tyurin's Theorem 5.1, which reproduces the same constant 16. The proof differs in two technical ways: it uses the closed-form step 1/(2ℓ(2‖g‖)) instead of the integral step, and it uses a fencing argument for the one-step descent. Neither is a new mechanism with complexity consequences.

**Search coverage:** I searched on 2026-11-21 (UTC). I read Tyurin's Thm 5.1, Cor. 5.2 and §5.3 verbatim from the arXiv HTML, and Vankov et al. Thm 3.1. I have only a summary of Li et al. Thm 5.2. I also looked at Chen et al. ([ICML 2023](https://proceedings.mlr.press/v202/chen23ar.html)) but did not check it in detail. The companion note's own statement that "the rate is not new" agrees with this assessment. The theorem was added in commit d4b14a20 (2026-11-21), more than a year after Tyurin's paper, so the question of whether a later result superseded it does not come up.

**Conclusion**

**No: this is a restatement of a known gradient-descent rate, not a new guarantee.** The strongest baseline is Tyurin's Theorem 5.1 (ICML 2025). It already bounds min ‖∇f_k‖²/ℓ(2‖∇f_k‖) by 4Δ/T for general ℓ. Plugging in the order-ρ regularity used here gives exactly

  ⌊16Δℓ(ε)/ε²⌋ + 1 (prior, by substitution) → ⌊16Δℓ(ε)/ε²⌋ + 1 (this result).

For the (L₀,L₁) case, Vankov et al. had already proved the same order with smaller constants.

The differences are technical. The step is closed-form rather than an integral, and ℓ may vanish at 0 or be discontinuous. The output is a frozen last iterate, which follows trivially from the best-iterate guarantee because gradient norms are observed. Meanwhile, the regularity requirement makes the theorem narrower than Tyurin's in ℓ. None of these changes the complexity, and none covers a meaningful new problem class.

What can be claimed is a formalized, closed-form-step version of Tyurin's nonconvex GD bound. Its role is to serve as the matching upper half of the companion lower bound; its novelty, if any, lies in that lower bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
