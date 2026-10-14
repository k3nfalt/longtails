# QuasarSignedBias: what is actually new?

The [theorem](../../LongTails/Theorems/QuasarSignedBias.lean) ([setup](../../LongTails/Setups/QuasarSignedBias.lean), [algorithm](../../LongTails/Algorithms/BestValueDescent.lean), [proof](../../LongTails/Proofs/QuasarSignedBias.lean)) makes the following guarantee. Take an everywhere-differentiable f on a real Hilbert space with ‖∇f‖ ≤ M that is τ-quasar-convex with respect to a global minimizer x\* with ‖x₀ − x\*‖ ≤ R. Each call k returns the exact value f(x) and the corrupted gradient ∇f(x) + b_{k+1} − b_k, where b₀ = 0 and ‖b_k‖ ≤ B for one fixed hidden sequence (b). Then gradient descent with η = τε/(M² + 2MB) returns the best-valued queried iterate, and that iterate satisfies f(x̂) − f(x\*) ≤ ε for every seed.

**Complexity.** Here M is the gradient bound, B the bound on the cumulative bias, R the initial distance, τ ∈ (0,1] the quasar parameter and ε the accuracy. The exact budget is K = max{1, ⌈R²(M² + 2MB)/(τ²ε²)⌉} value-and-gradient calls, that is

  **O(1 + R²M(M + B)/(τ²ε²))**,

with no batching, restarts or line search. The step size needs M, B, τ and ε, and the stopping rule also needs R. When B = 0 the method is plain subgradient descent with exact gradients.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jin, [arXiv:2010.04937v3](https://arxiv.org/pdf/2010.04937v3), Thm 5.1 (preprint, 27 Oct 2020); prior. Specialized to the deterministic case, B = 0 only | O(1 + R²M²/(τ²ε²)) (bound RG/(γ√T) with G = M, γ = τ, mean gap; take the best iterate using the exact values) → O(1 + R²M(M+B)/(τ²ε²)) | None: same order when B = 0. With B > 0 there is an extra R²MB/(τ²ε²) term, which Jin's theorem does not cover | Exact (or unbiased stochastic) gradients → gradients with telescoping bias; ℝⁿ → Hilbert space (Jin's argument is dimension-free) | None. The mean-gap bound already gives best-iterate accuracy | Deterministic oracle only (Jin also covers unbiased stochastic gradients); needs exact f values; Jin omits the proof as "relatively standard" |
| Karimireddy et al., EF-SGD, [ICML 2019](https://proceedings.mlr.press/v97/karimireddy19a.html), Thm III with proof in App. B.6 ([arXiv:1901.09847](https://arxiv.org/pdf/1901.09847)); prior. Restriction: convex f, compressor-generated error | Theorem: O(R²σ²(1+√(1−δ)/δ)²/ε²). Its proof with ‖e_t‖ ≤ γB in place of the compressor bound: O(1 + R²M(M+B)/ε²) for the averaged iterate → O(1 + R²M(M+B)/(τ²ε²)) | None: identical order when τ = 1 | Convex → τ-quasar-convex (e.g. √(1+x²) − 1 + 0.1(1 − cos x) is nonconvex, with \|f′\| ≤ 1.1 and τ = 0.9, checked numerically); compressor contraction → arbitrary bounded b | Averaged iterate → best-value iterate. Nonconvexity forces this change; it is not a gain | Requires differentiability rather than subgradients, exact function values and a deterministic oracle (EF allows stochastic gradients with E‖g‖² ≤ σ²) |

**Reduction check.** Set y_k = x_k + ηb_k. Then y_{k+1} = y_k − η∇f(x_k), and expanding ‖y_{k+1} − x\*‖² gives the bound −2ητ(f(x_k) − f\*) + η²(M² + 2MB), using quasar-convexity at x_k and |⟨∇f, b_k⟩| ≤ MB. This is line for line the virtual-iterate argument of Karimireddy et al.'s App. B.6 (x̃ = x − e, x̃_{t+1} = x̃_t − γg_t, then Cauchy–Schwarz on ⟨∂f(x_t), e_t⟩). Only two changes are needed: quasar-convexity replaces convexity in the single inequality evaluated at x_t, and the best iterate replaces the average. Optimizing η then gives the budget. I found no new mechanism or unresolved step. The [Stich–Karimireddy error-feedback framework](https://arxiv.org/abs/1909.05350) supplies the same virtual sequence for smooth problems; it is proof ancestry, not a baseline. In the repository, [QuasarAmortizedLMO](../../LongTails/Theorems/QuasarAmortizedLMO.lean) assumes smoothness, a bounded set and an LMO, so it is incomparable. No verified lower bound shows that the MB term or the τ⁻² factor is necessary.

**Search coverage (2026-10-07 UTC).** I read Jin's v3 §5 and Karimireddy et al.'s Thm III together with the full B.6 proof. Web and arXiv searches on nonsmooth or biased quasar-convex methods (Martínez-Rubio 2025; zeroth-order and high-order quasar-convex papers, 2025–26) and on inexact subgradient methods with bounded errors found no exact statement with arbitrary telescoping bias. Those papers assume per-step errors, smoothness or a different oracle, and I checked them only at the abstract level. There is no companion note. Git introduces the result at `e80ab93` (23 Sep 2026), so both baselines predate it. No build or axiom audit was run.

## Conclusion

**No: this is another analysis at the same complexity, obtained by combining two known proofs.**

The strongest baseline is the error-feedback analysis of Karimireddy et al. (ICML 2019). Its proof already handles gradient errors that telescope through a virtual iterate, but it is stated for convex f. Jin (2020) gives the matching quasar-convex subgradient rate, without bias.

| | calls for f(x̂) − f\* ≤ ε |
|---|---|
| Jin, B = 0 | O(1 + R²M²/(τ²ε²)) |
| EF proof with ‖e‖ ≤ ηB, τ = 1 | O(1 + R²M(M+B)/ε²) |
| this result | O(1 + R²M(M+B)/(τ²ε²)) |

The bound is the same order as each baseline wherever that baseline applies, and better in no parameter regime. The formally new instances are nonconvex quasar-convex functions observed through telescoping-biased gradients, and they need only a one-line substitution in the EF proof. In exchange, the result gives up stochastic noise and needs exact function values. Although I found no paper that states this exact combination, that absence does not make it substantive: the bound follows directly from known arguments.

What can be claimed is a clean formal statement of a standard corollary, the error-feedback virtual-iterate bound transferred to τ-quasar-convex Lipschitz functions.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
