# Alex-GDA on smooth convex–concave problems: novelty assessment

The [theorem](../../LongTails/Theorems/AlexGdaConvexConcave.lean) proves the following. Take the [setup](../../LongTails/Setups/BlockSmoothConvexConcave.lean) and run [constant-step Alex-GDA](../../LongTails/Algorithms/AlexGda.lean) with γ∈(1,2], δ≥1 and steps α=(γ−1)/(4γ²δ²(Lx+Lxy)), β=(γ−1)/(4γ²δ²(Ly+Lxy)). After the budgeted number of calls, the returned best-seen iterate ẑ (selected by a computed proxy at no extra cost) satisfies ‖∇ₓf(ẑ)‖²+‖∇ᵧf(ẑ)‖²≤ε² deterministically, for every differentiable convex–concave f on real Hilbert spaces E×F that has a saddle point.

**Proved complexity** (exact partial-gradient oracle, one call per block gradient):

  N = 2⌈180 γ⁴δ⁴ (max{Lx,Ly}+Lxy)² R² / ((γ−1)³ε²)⌉ = O(γ⁴δ⁴(max{Lx,Ly}+Lxy)²R²/((γ−1)³ε²)) + 2.

Here Lx and Ly are the within-block Lipschitz constants of the partial gradients, Lxy is the cross-block constant, R bounds the distance from (x₀,y₀) to a saddle point and ε is the target gradient norm. The constant is at least 2880(max{Lx,Ly}+Lxy)²R²/ε², with this minimum at γ=2. The bound degrades as γ↓1 or as δ grows.

**Reduction to monotone operators.** Let F=(∇ₓf,−∇ᵧf). F is monotone, and the block inequalities make it Λ-Lipschitz with Λ=max{Lx,Ly}+Lxy (the spectral norm of [[Lx,Lxy],[Lxy,Ly]] is at most Λ). Also ‖F(z)‖²=‖∇ₓf‖²+‖∇ᵧf‖². Conversely, if F is L-Lipschitz then Lx,Ly,Lxy≤L. So the target class is, up to a factor of 2 in the constant, the class of smooth convex–concave problems. One evaluation of F costs two block calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Yoon–Ryu, EAG-V, [ICML 2021, Cor. 2](https://proceedings.mlr.press/v139/yoon21d/yoon21d.pdf) (arXiv v2 2021-06-10; stated on ℝⁿ×ℝᵐ). Its lower bound (Cor. 3) shows this rate is optimal for span-type methods. | 4⌈√27·ΛR/ε⌉ = O(1+ΛR/ε) → O(γ⁴δ⁴Λ²R²/((γ−1)³ε²)+1) | Worse: by a factor ≳ΛR/ε whenever ΛR≥ε/30. Both are O(1) below that threshold. | None. Stated in finite dimension, but the proof uses only inner products; repository [AnchoredGeneralizedMonotone](../../LongTails/Theorems/AnchoredGeneralizedMonotone.lean) (L₁=0, any inner-product space, introduced earlier at `bf9edbc`) gives O(1+ΛR/ε+log(1+ΛR/ε)) | Worse: last iterate → best-seen iterate | Alex-GDA needs Lx, Ly, Lxy separately; EAG needs only Λ. Both need R and ε for stopping. |
| Gorbunov–Taylor–Gidel, past extragradient / OGDA, [NeurIPS 2022, Thm 1](https://arxiv.org/abs/2205.08446) (v2 2022-10-31) | 2(⌈123Λ²R²/ε²⌉+1) = O(1+Λ²R²/ε²) → O(γ⁴δ⁴Λ²R²/((γ−1)³ε²)+1) | None: same order for fixed γ,δ. Alex-GDA's constant is ≥10× larger. | None | Worse: last iterate → best-seen iterate | Both use one new gradient per block per iteration, so the oracle access is the same. |
| Shugart–Wang–Altschuler, alternating GDA with momentum −½, [arXiv 2604.17145v1, Thm 3.1](https://arxiv.org/html/2604.17145v1) (preprint, 2026-04-18, **prior**). Applies to L-smooth f; take L=Λ. | O(1+Λ²R²/ε²) in expectation over a random iterate → same order, deterministic best-seen iterate | None: same order | None | Deterministic selected iterate vs random iterate. Converting their result costs extra residual evaluations. | Different algorithm (negative momentum, not extrapolation) |

**Reduction check and proof ancestry.** The rate is not a corollary of operator theory. The note's counterexample suggests block-wise extrapolation genuinely uses the saddle structure, and the [step lemma](../../LongTails/Proofs/AlexGdaStep.lean) relies on a Lyapunov energy with cross and function-value terms. Even so, no complexity gain survives the reduction to a Λ-Lipschitz monotone operator, where EAG and PEG apply directly. [Lee–Cho–Yun (ICML 2024, arXiv v2 2024-07-15)](https://arxiv.org/abs/2402.10475) Thm 5.1 assumes twice-differentiable strongly-convex–strongly-concave f with γ,δ>1. I verified those hypotheses; it gives no conclusion at μ=0. Their Conjecture 8.2 (verified) asks for last-iterate convergence for convex–concave f. The Lean result gives only a best-iterate stationarity rate. Iterate convergence is argued on paper only, contrary to the companion note's "establishes … the convergence asserted in Conjecture 8.2."

**Search coverage** (2026-10-07 UTC): arXiv, ICML, NeurIPS and ICLR sources on Alex-GDA, the prediction method, OGDA/EG last-iterate results and anchored methods, plus forward searches citing Lee–Cho–Yun. I found no prior convex–concave guarantee for unmodified Alex-GDA. The full texts of the 2024–2025 nonlinear-PDHG papers ([Wu–Liu](https://doi.org/10.1016/j.apnum.2024.12.010), [Liu–Zhang](https://doi.org/10.1080/02331934.2025.2601995)) and of Shugart–Altschuler's [negative-stepsize paper](https://arxiv.org/abs/2505.01423) were not checked. The result entered the repository in `89400cf` (2026-10-03). I did not run a build.

**Conclusion**

**No: this is another analysis of one method, not an improvement in complexity or scope.**

The strongest baseline is extra anchored gradient (EAG), on the same smooth convex–concave class with the same block-gradient oracle:

| method | calls to reach ‖∇f‖≤ε | output |
|---|---|---|
| this result (Alex-GDA) | O(γ⁴δ⁴Λ²R²/((γ−1)³ε²)+1) | best-seen iterate |
| EAG (Yoon–Ryu) | O(1+ΛR/ε) | last iterate |
| optimistic GDA (Gorbunov et al.) | O(1+Λ²R²/ε²) | last iterate |

Here Λ=max{Lx,Ly}+Lxy. Whenever ΛR≥ε/30, EAG's bound is smaller by a factor of order ΛR/ε. Optimistic GDA already matches the ε-rate with a last-iterate guarantee. The block-Lipschitz class is no larger than the smooth convex–concave class (the constants differ by at most a factor of 2), and covering infinite-dimensional Hilbert spaces is not an advantage, because anchored methods' proofs are dimension-free and the repository already formalizes one.

What is established is a global constant-step rate for unmodified Alex-GDA without strong convexity. This partially addresses Lee–Cho–Yun's Conjecture 8.2 (a best-iterate rate, not last-iterate convergence). My search found no earlier such result, but that does not prove priority, and some related full texts were not checked. The claimable contribution is a method-specific convergence analysis, not a better optimization guarantee. This agrees with the user-reviewed negative example for this result.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
