# Novelty assessment: NoisyTwoSampleQuadraticPerceptron

The [theorem](../../LongTails/Theorems/NoisyTwoSampleQuadraticPerceptron.lean) shows the following for the noisy, violation-priority two-sample quadratic perceptron ([setup](../../LongTails/Setups/NoisyTwoSamplePerceptron.lean), [algorithm](../../LongTails/Algorithms/NoisyTwoSamplePerceptron.lean)). The model is the kernel-2 convolutional classifier on Tyurin's dataset (5), with the perturbed coordinate at a hidden cyclic index `i`. The method uses `γ = 1/(4√d)` and Gaussian noise `σ = s/(4096 T √max{d, log(T/ρ)})`. With probability at least `1−ρ`, the last iterate strictly separates both samples after `2T` sample queries.

**Bound.** The parameters are as follows:
- `d ≥ 2` is the dimension.
- `0 < μ ≤ 1/10` is the margin perturbation.
- `x₀` is the fixed initialization.
- `s` is a known lower bound with `0 < s ≤ |⟨x₀, v_{μ,+}⟩|`, the projection onto the slow eigenvector at index `i`. Since `s ≤ ‖x₀‖`, the ratio `‖x₀‖/s ≥ 1`.
- `ρ ∈ (0,1)` is the failure probability.

The public budget is `2⌈K log K⌉` with `K = 2²⁷(√d/μ) log(2⁶²‖x₀‖²/(ρ³s²)) log(2¹⁵√d‖x₀‖²/(μs²))`. Simplified, this is

  `O( (√d/μ) · log(‖x₀‖²/(ρ s²)) · log(d‖x₀‖²/(μ s²)) · log( (d/μ)·log(‖x₀‖²/(ρ s²)) ) )` queries.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2512.11587](https://arxiv.org/abs/2512.11587) v1 12 Dec 2025, v2 21 May 2026; [ICML 2026, PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html), **Thm 5.1**: the same noisy priority QPA, `γ = 1/(4√d)`, dataset (5). | `T = ⌈A log(A√d/μ)·√d/μ⌉` steps, with `A = 2²⁷ log(2⁶²‖θ₀‖²/(ρ³⟨θ₀,v⟩²)) log(2¹⁵√d‖θ₀‖²/(μ⟨θ₀,v⟩²))`. That is at most 2 sample evaluations per step, so `2T` queries → the identical `2⌈K log K⌉` with `s = |⟨x₀,v⟩|`. | None: identical formula and constants. | Exact projection in the noise tuning → any lower bound `s` (a smaller `s` raises the budget). Fixed index 1 → hidden cyclic index, which is the same problem up to a coordinate relabeling. | None. Same output (last iterate, frozen at a separator) and same probability-`1−ρ` criterion. | None found. The Lean version counts both sample queries per round explicitly; the paper counts steps. |
| Repository: [TwoSampleQuadraticPerceptronAcceleration](../../LongTails/Theorems/TwoSampleQuadraticPerceptronAcceleration.lean), the noiseless priority QPA introduced 2026-10-23. | `O((√d/μ)·log ρ'·(log ρ' + log(dS/(μ a z))))` deterministic on an initialization cone, with `ρ'` a slow-block ratio → the bound above, with probability `1−ρ`. | Not comparable: different initialization classes and probability criteria. | This result: any `x₀` with nonzero slow projection, versus the cone, which holds about 1/4 of Gaussian mass. The cone result instead covers general data and a two-layer model. | Deterministic → probability `1−ρ`. | Needs injected noise tuned to `s`, `T`, and `ρ`. |
| Unrestricted algorithm, same oracle (checked directly). | `O(1)` queries: one query at `c = e₁, v = 0` returns the gradient `lift(b₂)`, which reveals `i`, and an explicit separator can then be output → `Θ̃(√d/μ)`. | Worse: by a factor of `Θ̃(√d/μ)`. | None. | None. | `allowedAlgorithm` fixes the update family, so the result is a method-specific analysis. |

**Reduction check and mechanism.** Up to the trivial cyclic relabeling and the replacement of the exact projection by the certificate `s`, the statement is Tyurin's Theorem 5.1 with the same constants. The companion note explicitly calls it a reproduction. The proof outline in the note matches the paper's approach: Gaussian-noise block estimates, a union bound over starts, and counting second-sample moves. I did not compare the Lean proof steps line by line with Appendix C. Allowing a lower bound `s` is a monotone weakening of the tuning input and is not independently significant.

**Search coverage.** I searched on 2026-11-25 UTC: the arXiv v1/v2 pages, the verbatim v2 HTML for Section 5 (Theorems 5.1 and 5.2; the appendix was not read), the PMLR and ICML 2026 listings, and web searches for follow-ups. I found no later work on this setup. The companion note's citations and its "reproduction" claim are consistent with these sources. The theorem was introduced in commit `f2d9aff8` (2026-11-25), after the paper.

**Conclusion**

**No: this is a formal reproduction of a published theorem, not a new result.**

The strongest baseline is Tyurin's Theorem 5.1 (ICML 2026). It proves the same guarantee for the same noisy priority perceptron, with the same step size, noise formula, initialization condition, and iteration bound:

| | Queries to separate w.p. `1−ρ` |
|---|---|
| Tyurin Thm 5.1 (2 queries/step) | `2⌈A log(A√d/μ)·√d/μ⌉` |
| This theorem | `2⌈K log K⌉`, with `K = A√d/μ` (the same quantity) |

The only differences are cosmetic. The perturbed coordinate is a hidden cyclic index, a relabeling of the paper's fixed index. The noise is tuned to a lower bound `s` on the slow projection rather than its exact value, and a smaller `s` only enlarges the budget.

Separately, finding a separator in this oracle model is not hard: one gradient query reveals the hidden index, so `O(1)` queries suffice. Like the paper's, the result is therefore about one method's dynamics, not problem-class complexity. What can be claimed is a machine-checked Lean proof of Tyurin's Theorem 5.1, with explicit query counting. That has value as verification but is not mathematical novelty.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
