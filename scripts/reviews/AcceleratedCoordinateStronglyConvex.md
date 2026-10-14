# Novelty assessment: AcceleratedCoordinateStronglyConvex

The [theorem](../../LongTails/Theorems/AcceleratedCoordinateStronglyConvex.lean) proves the following. Let f on ℝᵈ be differentiable and μ-strongly convex (Euclidean norm), satisfy the coordinate upper model f(x+teᵢ) ≤ f(x)+t∂ᵢf(x)+Lᵢt²/2, and have a minimizer with f(x₀)−f* ≤ Δ. After the budgeted number of exact partial-derivative queries, the last iterate y_K of the non-uniformly sampled [accelerated coordinate method](../../LongTails/Algorithms/AcceleratedCoordinate.lean) satisfies E f(y_K) − f* ≤ ε ([setup](../../LongTails/Setups/CoordinateSmoothStronglyConvex.lean)).

**Complexity** (∂ᵢf calls): the budget is K = 2·Σᵢ max(1,⌈√(Lᵢ/μ)⌉)·⌈log₂⌈2Δ/ε⌉⌉. This gives

  **O( Σᵢ₌₁ᵈ √(Lᵢ/μ) · log(2 + Δ/ε) )**,

where Lᵢ are the coordinate smoothness constants, μ is the strong-convexity modulus, Δ is the initial gap, and ε is the target expected gap. The hypotheses force μ ≤ Lᵢ, so max(1,⌈√(Lᵢ/μ)⌉) ≤ 2√(Lᵢ/μ). When Δ ≤ ε/2, K = 0 and the output is x₀. The proof ([Convergence](../../LongTails/Proofs/AcceleratedCoordinateConvergence.lean), `run_rate`) gives E f(y_K) − f* ≤ (1−1/(2S))^K·2Δ, where S = Σᵢ max(1,⌈√(Lᵢ/μ)⌉). The sampling probability is pᵢ = max(1,⌈√(Lᵢ/μ)⌉)/S. Both the updates and the budget need every Lᵢ and μ.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Allen-Zhu, Qu, Richtárik, Yuan, NU_ACDM, [arXiv:1512.09103 v3](https://arxiv.org/abs/1512.09103) (27 May 2016; ICML 2016), Thm 5.1, β=0 | E f(y_T)−f* ≤ O(1)(1−τ)^T(f(x₀)−f*) with τ = 1/O(Σᵢ√Lᵢ/√μ), so O(Σᵢ√(Lᵢ/μ)·log(2+Δ/ε)) → O(Σᵢ√(Lᵢ/μ)·log(2+Δ/ε)) | None: same order. The Lean τ = 1/(2S) and the rounded weights cost constant factors only. | None. Def. 4.2 (Lipschitz ∂ᵢf) is equivalent, for convex f, to the coordinate quadratic upper model used here. Lemma 5.3, the only use of smoothness, needs only that model. | None: both give the expected gap of the last iterate y_T, and both need Lᵢ and μ. | Integer-rounded probabilities ⌈√(Lᵢ/μ)⌉ instead of √Lᵢ; worse constants. The algorithm is otherwise identical: x=τz+(1−τ)y, y=x−∂ᵢf/Lᵢ, z=(z+ημx−η∂ᵢf/pᵢ)/(1+ημ). |
| Nesterov & Stich, [CORE DP 2016/03](https://research.dial.uclouvain.be/bitstreams/17030fdd-b954-42ab-846b-bde726552e58/download) (1 Feb 2016; SIAM J. Optim. 27(1), 2017), Thm 1, α=1 (probabilities ∝ √Lᵢ) | 2A_t(E f(x_t)−f*) ≤ ‖x₀−x*‖² ≤ 2Δ/μ, with A_t ≥ ((1+γ)^t−(1−γ)^t)²/(4μ) and γ = √μ/(2Σ√Lᵢ). This gives O(Σᵢ√(Lᵢ/μ)·log(2+Δ/ε)) → same | None: same order. | None. Eq. (2.3)–(2.4) state the same coordinate-smoothness class, which also covers block coordinates. | None: both give the expected gap of the last iterate. | None beyond constants. NS also has a smooth-convex O(Σ√Lᵢ·R/√ε) bound, which this theorem does not cover. |

Lee–Sidford ACDM (FOCS 2013) reportedly needs O(√(d·ΣLᵢ/μ)·log(1/ε)), according to Nesterov–Stich Remark 1. Both rows above already improve on it by up to √d, so it is not a stronger baseline.

**Reduction check / proof ancestry.** The theorem is NU_ACDM with β=0. It uses the same coupling, the same y/z updates, the same 1/pᵢ-weighted mirror step, and the same potential f(y)−f*+(μ/2)·‖z−x*‖²·const (Lemmas 5.3–5.6). The guarantee therefore follows by direct specialization of Thm 5.1, with initial potential ≤ 2Δ by strong convexity. I found no new mechanism. Linear coupling (Allen-Zhu–Orecchia) and Nesterov's estimate sequences are proof ancestry only.

**Search coverage** (2026-10-07). I read the theorem texts of arXiv:1512.09103v3 (Thm 5.1, Defs. 4.1–4.3, Lemma 5.3) and the Nesterov–Stich discussion paper (§2, Thm 1, Remark 1). I did not read Lee–Sidford's text, and I did not check the final SIAM version. The theorem entered the repository in commit b3d990f (2026-09-23), about ten years after both papers. There is no companion note. No other repository theorem treats coordinate methods; the prior repository review reached the same conclusion, and I checked it independently. I make no optimality claim.

## Conclusion

**No: this is a re-proof of a known result, with the same complexity, assumptions, and output.**

The strongest baseline is NU_ACDM (Allen-Zhu–Qu–Richtárik–Yuan, ICML 2016, Thm 5.1 with β=0). It runs the same algorithm with sampling ∝ √Lᵢ on the same class: coordinate-smooth, μ-strongly convex f with exact partial-derivative queries. It bounds the expected gap of the last iterate y_T. Nesterov–Stich (SIAM J. Optim. 2017, Thm 1) independently gives the same order.

| | ∂ᵢf calls for E f(y)−f* ≤ ε |
|---|---|
| NU_ACDM / Nesterov–Stich | O(Σᵢ√(Lᵢ/μ)·log(2+Δ/ε)) |
| This theorem | O(Σᵢ√(Lᵢ/μ)·log(2+Δ/ε)) |

The orders agree in every parameter regime. The Lean version is worse by constant factors because of its halved τ and integer-rounded weights. Its coordinate quadratic upper model is equivalent, for convex f, to the Lipschitz-partial-derivative assumption of the prior work, so no instances are added. Both results require all Lᵢ and μ.

What can be claimed is a Lean formalization of the known non-uniform accelerated coordinate descent guarantee. That is not a new mathematical result.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
