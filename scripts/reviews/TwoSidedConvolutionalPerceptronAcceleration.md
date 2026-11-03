# Novelty assessment: TwoSidedConvolutionalPerceptronAcceleration

[Theorem](../../LongTails/Theorems/TwoSidedConvolutionalPerceptronAcceleration.lean) proves the following. Use exact margin/gradient queries on the model `m(b;(c₁,c₂),v) = c₁⟨b,v⟩ + c₂⟨Pb,v⟩`, with [setup](../../LongTails/Setups/TwoSidedConvolutionalPerceptron.lean) samples `D_i = α_i e + μu_i`. Then the cyclic quadratic perceptron ([algorithm](../../LongTails/Algorithms/TwoSidedConvolutionalPerceptron.lean)) separates all `N` samples deterministically, for every oracle seed. It starts at `((1,0),0)`, uses step `η = κ/(96R)`, and outputs its last iterate. The required geometry is `e = 1/√d`, `u_i ⊥ e`, `‖u_i‖ ≤ 1/√2`, and `g ≤ |α_i| ≤ R`.

**Oracle complexity** (`N` = number of samples; `g, R` = lower and upper background intensity; `μ` = contrast; `κ` = margin of the derivative features `r_i = (u_i − Pu_i)/√2` with respect to an unknown unit `w`):

  `N · ⌈2²⁴ (R/g)² (1 + log(1 + g/μ)) / κ³⌉`  calls,

valid only when `μκ⌈2²⁴(R/g)²(1+log(1+g/μ))/κ³⌉ ≤ 3R/2`. This holds, for example, if `μ ≤ κ⁴g³/(2⁵⁰R²)`. Note that `κ ≤ ‖r_i‖ ≤ 1`.

`allowedAlgorithm` restricts the method to this family and compliance is proved. Quadratic perceptron (QPA) is not a GD/SGD/Adam-level family, so I compare it with methods for the underlying problem as well.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Read-and-solve (elementary). One query at `((1,0),v)` per sample returns `D_i` as the `v`-gradient. Then solve an LP offline for `v` on the features `(D_i − PD_i)/√2 = μr_i` (because `Pe = e`). Output `((1/√2,−1/√2),v)`. | `N` → `N⌈2²⁴(R/g)²(1+log(1+g/μ))/κ³⌉` | Worse: by a factor `≥ 2²⁴(R/g)²/κ³`, for all parameters | None. The baseline needs no parameters and no small-`μ` regime. | Worse: the baseline needs no knowledge of `g,R,μ,κ`. | The baseline uses offline computation and lies outside the QPA family. |
| Fixed-filter perceptron (Novikoff 1962). Cyclic perceptron on `v` with `c` frozen at `(1/√2,−1/√2)`. The replies are `μr_i` with margin `μκ` and norm `≤ μ`. | `N(⌊1/κ²⌋+1)` → `N⌈2²⁴(R/g)²(1+log(1+g/μ))/κ³⌉` | Worse: the baseline is independent of `μ`, `g`, and `R` | None | None: both return the last iterate and both are deterministic. | The baseline uses the same oracle and is online, but it does not update the filter, so it falls outside `family`. |
| Tyurin, [arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587v2) (21 May 2026; [ICML 2026, PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html)), Thms 5.1/5.2 | 2-sample QPA `Õ(√d/μ)` w.h.p. (vs. batch linear perceptron `Ω(d/μ)`) → not comparable | Not comparable: the instance classes are disjoint | Two samples, dataset (5) → `N` samples with two-sided intensities. Dataset (5) itself is **excluded**: `b₁ = 1_d` has `r_1 = 0`, so `κ = 0`. | Gaussian-perturbed generic start → deterministic identity start (the note itself calls this the favourable regime) | Margin-tuned step `κ/(96R)` instead of `Θ(1/R)`, and a tiny-`μ` regime |
| Repo [Clustered](../../LongTails/Theorems/ClusteredConvolutionalPerceptronAcceleration.lean) (prior commit) | `N(128(R/g)²log(16R²/μ²)+3)` on its class → this bound on this class | Not comparable. Where both apply, this bound is worse by a factor `κ⁻³`. | Removes the cluster cap `‖u_i−u⋆‖ ≤ κ/64` and the κ-dependent start. Neither class contains the other. | None | Worse dependence on `κ` |

**Reduction check:** the guarantee does not follow from any known QPA theorem. The contraction-plus-potential argument for the coupled `(a,q)`/`(t,z)` system appears to be a new method-specific analysis. Proof ancestry is Tyurin's QPA reduction and Novikoff-style progress/norm comparison. The problem itself, however, reduces trivially. Freezing the filter at the difference kernel removes the background exactly, leaving a standard linear-separability problem with margin `κ`.

**Search coverage:** searches on 2026-11-01 UTC covered arXiv, PMLR, and general web results for QPA follow-ups and many-sample implicit-acceleration bounds, and found none. I verified Tyurin's Thms 5.1/5.2 from the v2 HTML. I did not reread the later sections of the paper or the OpenReview items. The companion note is accurate here: it disclaims any problem-class complexity and the comparability with Thm 5.1, and it acknowledges that dataset (5) is excluded.

## Conclusion

**No: the theorem gives another analysis of one method, not a better way to solve this problem.** The strongest baseline uses the same oracle and freezes the convolution filter at the difference kernel. That kernel removes the shared background exactly, and an ordinary perceptron then finishes:

| Method (same oracle, same strict-separation output) | Calls |
|---|---|
| Query each sample once, then solve an LP offline | `N` |
| Fixed-filter cyclic perceptron | `N(⌊1/κ²⌋+1)` |
| This result | `N⌈2²⁴(R/g)²(1+log(1+g/μ))/κ³⌉`, only for tiny `μ` |

The selected bound is worse in every regime. It also needs `g,R,μ,κ` for its step size and validity condition.

What is established is a method-level fact: the QPA dynamics, with the filter learned from the identity start, separate an `N`-sample, two-sided class in `O(N log(1/μ))` calls when `κ` and `R/g` are fixed. Linear zero-initialized perceptrons need `Ω(1/μ)` on an explicit subfamily. This extends Tyurin's two-sample implicit-acceleration phenomenon to more samples. However, it does not cover Tyurin's own dataset or his random-start regime, and it uses a margin-tuned step.

My search found no prior many-sample finite-time QPA bound, but that does not establish priority. The contribution that can be claimed is a new deterministic analysis of convolutional-perceptron dynamics on a tailored class. It is not an improved oracle complexity or a meaningful new problem setup.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
