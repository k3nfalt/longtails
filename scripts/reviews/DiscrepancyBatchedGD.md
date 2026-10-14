# Novelty assessment: batched GD under relative temporal discrepancy (PL)

The [theorem](../../LongTails/Theorems/DiscrepancyBatchedGD.lean) proves the following, using the [setup](../../LongTails/Setups/RelativeDiscrepancyPL.lean) and [algorithm](../../LongTails/Algorithms/DiscrepancyBatchedGD.lean). Let f be differentiable and L-smooth on a real inner-product space, with an attained minimum, globally μ-PL, and f(x₀)−f* ≤ Δ. Its deterministic oracle replies g_k(x) satisfy ‖Σ_{i<n}(g_{s+i}(x)−∇f(x))‖ ≤ D‖∇f(x)‖ for all s, n and x. Gradient descent with step 1/L uses the average of B = max(1,⌈2D⌉) consecutive replies at the same point for each step. Its **last iterate** satisfies f(x_K)−f* ≤ ε for every seed.

**Oracle complexity.** The proved budget is max(1,⌈2D⌉)·⌈(4L/(3μ))·log(1+Δ/ε)⌉, which is

  **N = O((1+D)·(1 + (L/μ)·log(1+Δ/ε)))** calls, for 0 < μ ≤ L, D ≥ 0, Δ ≥ 0, ε > 0.

Here L is the smoothness constant, μ the PL constant, D the relative discrepancy, Δ the initial gap and ε the target gap. The updates need L and D. The budget also needs μ, Δ and ε.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Puchinin–Stonyakin, [arXiv:2307.14101v3](https://arxiv.org/html/2307.14101v3), §3, eqs. (9)–(11) (preprint; v3 dated 2023-12-10), implemented by batching ⌈3D⌉ calls | max(1,⌈3D⌉)·⌈(4L/μ)log(1+Δ/ε)⌉ = O((1+D)(1+(L/μ)log(1+Δ/ε))) → O((1+D)(1+(L/μ)log(1+Δ/ε))) | None: same order; only the constant changes (4 → 4/3) | ℝⁿ → general inner-product space. This is a routine extension, because their proof uses only inner products. | None: both give deterministic last iterates with fixed steps. | Their oracle is a relative-error oracle, ‖g̃−∇f‖ ≤ α‖∇f‖ with α < ½. Averaging ⌈3D⌉ consecutive replies gives α ≤ 1/3, and their descent step (10) is pointwise, so time-varying replies are allowed. |
| Special case D = 0: exact GD under PL ([Karimi–Nutini–Schmidt, Thm 1](https://arxiv.org/abs/1608.04636), ECML-PKDD 2016; Polyak 1963) | ⌈(L/μ)log(Δ/ε)⌉ → ⌈(4L/(3μ))log(1+Δ/ε)⌉ | None: same order | None | None | Applies only to exact gradients. |
| Special case, strongly convex subclass only: RE-AGM, [Vasin et al., arXiv:2503.06628v3, Thm 4](https://arxiv.org/html/2503.06628v3) (v3 dated 2025-12-09), implemented by batching ⌈D/α⌉ calls with α ≈ 0.016√(μ/L) | O((√(L/μ) + D·L/μ)·log(1+LΔ/(με))) → O((1+D)(1+(L/μ)log(1+Δ/ε))) | Worse in one regime and not better in the other. If D ≤ √(μ/L), RE-AGM costs O(√(L/μ)·log(1+LΔ/(με))) while this result costs Θ((L/μ)·log(1+Δ/ε)). If D ≥ 1, both are Θ(D(L/μ)·log), up to a log(L/μ) factor in RE-AGM. | PL → strongly convex is a strict restriction for RE-AGM, so the classes are nested and RE-AGM covers fewer instances. | None | RE-AGM requires strong convexity and μ. I used R² ≤ 2Δ/μ. I did not verify that their proof allows time-varying replies at repeated query points. |

**Reduction check.** Dividing the window bound by B gives a relative-error gradient with α = D/B ≤ ½. The [proof](../../LongTails/Proofs/DiscrepancyBatchedGD.lean) then applies the standard descent inequality and the PL contraction. No new mechanism is needed, and the theorem is a direct composition of batching with known relative-error GD. For D ≤ O(1) the rate matches the Ω((L/μ)·log(1/ε)) first-order lower bound for smooth PL functions ([Yue–Fang–Lin, COLT 2023](https://arxiv.org/abs/2212.13551)). That lower bound is inherited and is not an improvement. I have not verified any lower bound showing that the (1+D) factor is necessary.

**Search coverage.** I searched on 2026-10-07 UTC across arXiv, ICML/COLT/ECML pages, and the relative-error and bounded-error gradient literature. I did not access Polyak's 1987 book or the Vasin–Gasnikov 2026 preprint (arXiv:2603.12376) in full. I found no prior paper that states this exact partial-sum oracle condition. Git introduces the result in `55b5768` on 2026-09-23, after all the cited works. There is no companion Markdown note.

**Conclusion**

**No: this is a routine corollary of known results, with no gain in complexity or scope.** The partial-sum condition only says that averaging ⌈2D⌉ consecutive replies gives a gradient with relative error ½. Gradient descent with that kind of error is already known to converge linearly under PL (Puchinin–Stonyakin 2023, following Polyak).

| | Calls |
|---|---|
| Batched Puchinin–Stonyakin | O((1+D)(1+(L/μ)log(1+Δ/ε))) |
| This result | O((1+D)(1+(L/μ)log(1+Δ/ε))) |

The two bounds have the same order in every regime, and the same reduction covers time-varying replies. On strongly convex instances with D ≤ √(μ/L), batched accelerated methods are faster by about √(L/μ). For D = O(1), no first-order method can beat this rate on the full PL class.

The oracle condition may not appear in the literature in this exact form, but it has no independent motivation in the theorem, and it is removed by a two-line reduction. What can be claimed is a clean Lean formalization of batched inexact GD under PL, not a new optimization guarantee.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
