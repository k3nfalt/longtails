# GdPL: gradient descent on smooth Polyak–Łojasiewicz objectives

[`result`](../../LongTails/Theorems/GdPL.lean) shows the following. Take any real Hilbert space, an objective with an `L`-Lipschitz gradient, a global minimizer `xstar` with `f x0 − f xstar ≤ Δ`, and the PL inequality `2μ(f x − f xstar) ≤ ‖∇f x‖²` with `0 < μ ≤ L` ([setup](../../LongTails/Setups/SmoothPL.lean)). Then the last iterate of gradient descent with step size `1/L` ([algorithm](../../LongTails/Algorithms/Gd.lean)) satisfies `f x_K − f xstar ≤ ε` after `K = ⌈(L/μ) log(1 + Δ/ε)⌉` exact-gradient calls. The guarantee is deterministic: oracle replies are forced to equal `∇f`.

**Complexity.** The bound uses `L` (gradient-Lipschitz constant), `μ` (PL constant), `Δ` (bound on the initial objective gap) and `ε` (target objective gap):

  **O( (L/μ) · log(1 + Δ/ε) + 1 )** gradient calls. When `Δ = 0` the budget is 0.

The updates need `L` and `x0`. The budget, which acts as the stopping rule, also needs `μ`, `Δ` and `ε`. The proof ([`Proofs/GdPL.lean`](../../LongTails/Proofs/GdPL.lean)) has three steps. First, the descent lemma. Second, the PL inequality gives the contraction `(1 − μ/L)^k Δ`. Third, the bound `1 − t ≤ e^{−t}`. There is no companion note.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Polyak 1963 (*Zh. Vychisl. Mat. Mat. Fiz.* 3:643–653), as restated and reproved in Karimi–Nutini–Schmidt, [arXiv:1608.04636v4](https://arxiv.org/abs/1608.04636), **Theorem 1** (ECML-PKDD 2016) | `f(x_k) − f* ≤ (1 − μ/L)^k (f(x0) − f*)`, so `⌈(L/μ) log(Δ/ε)⌉` calls → `⌈(L/μ) log(1 + Δ/ε)⌉` | None: identical contraction. The `1+` inside the log only makes the formula valid when `Δ < ε`. | Karimi et al. state the result for ℝ^d with a nonempty solution set. The Lean version works in a general Hilbert space. Their proof uses only the descent lemma and the PL inequality, so it carries over word for word; this is not a meaningful relaxation. | None. Both are last-iterate, deterministic results with step `1/L`. | The Lean version additionally assumes a global minimizer and a known bound `Δ`. Otherwise the two are the same. |
| Lower bound (not a competing method): Yue–Fang–Lin, [arXiv:2212.13551v2](https://arxiv.org/abs/2212.13551), **Theorems 2–3**, COLT 2023 ([PMLR 195:2948–2968](https://proceedings.mlr.press/v195/yue23a.html)) | Any deterministic first-order method needs `Ω((L/μ) log(1/ε))` calls when `κ = L/μ` exceeds a universal constant and `ε ≤ Δ/16` (gap measured relative to the initial gap) → this result achieves `O((L/μ) log(Δ/ε))` | None possible beyond constants for deterministic first-order methods in that regime. | None | None | The lower bound covers deterministic algorithms only; it is not proved for randomized ones. |

**Reduction check.** The result is the textbook theorem itself, not a corollary of it. The only additions are the iteration count obtained by inverting `(1 − μ/L)^K Δ ≤ ε` and the general Hilbert-space domain. Neither involves a new mechanism or an unresolved obstacle. Repository overlap: several proofs ([`DriftCorrectedGD`](../../LongTails/Proofs/DriftCorrectedGD.lean), [`RobustPolyak`](../../LongTails/Proofs/RobustPolyak.lean), [`DiscrepancyBatchedGD`](../../LongTails/Proofs/DiscrepancyBatchedGD.lean)) reuse its `geometric_budget` lemma. The result was introduced in commit `84c49c5` (2026-09-23), nearly 63 years after Polyak.

**Search coverage (2026-10-07 UTC).** I read Theorem 1 of Karimi et al. (v4, 12 Sep 2020) and Theorems 2–3 and the concluding discussion of Yue et al. (v2, 2 Aug 2023), and confirmed the COLT 2023 publication. I did not access Polyak's original 1963 Russian text, so I rely on Karimi et al.'s attribution of the first proof to it. Since Yue et al. show the method is optimal, no later improvement to this deterministic rate is possible beyond constants.

## Conclusion

**No: this is Polyak's 1963 linear-convergence theorem for gradient descent, restated with an explicit iteration count.**

The closest baseline is Theorem 1 of Karimi–Nutini–Schmidt (2016), which reproves Polyak's result. It assumes the same things: an `L`-smooth objective satisfying the μ-PL inequality, step `1/L`, and a last-iterate guarantee. It proves the same contraction, which gives the same budget:

| | Gradient calls for `f(x_K) − f* ≤ ε` |
|---|---|
| Polyak 1963 / Karimi et al. Thm 1 | `(L/μ) log(Δ/ε)` |
| This result | `⌈(L/μ) log(1 + Δ/ε)⌉` |

The extensions are cosmetic. The domain is a general Hilbert space instead of ℝ^d, but the classical proof never uses the dimension. The `1+` inside the log only covers the case `Δ < ε`.

Yue–Fang–Lin (COLT 2023) show that no deterministic first-order method beats `Ω((L/μ) log(1/ε))` on this class once `L/μ` is large. So the rate is optimal up to constants and offers no room for a new complexity claim. That lower bound is about the problem class, not about who proved the upper bound first. The priority question is settled separately by the explicit 1963 attribution.

What can be claimed is a correct Lean formalization of a classical result and a reusable budget lemma, not a mathematical contribution.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
