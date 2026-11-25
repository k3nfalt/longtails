# Logistic GD on translated defect clouds: novelty assessment

[`result`](../../LongTails/Theorems/LogisticDefectCloudGradientDescent.lean) proves that full-batch logistic GD on the two-tap bilinear model `h⟨Sx,w⟩ + t⟨Tx,w⟩` reaches an iterate that strictly classifies all `2n` indexed observations with probability `≥ 1−ρ`. The algorithm uses step `1/(2⁴⁸L(a+μ))`, starts on a random sphere of radius `r`, and stops at the first fully correct pass. The data must satisfy the exact orthogonal reference/defect/residual geometry in [the setup](../../LongTails/Setups/LogisticDefectCloud.lean). The [algorithm](../../LongTails/Algorithms/LogisticDefectCloud.lean) is enforced through `allowedAlgorithm := family`.

**Proved complexity** (margin/gradient oracle calls, padding included):

  `O( n (1 + a/μ) log(1/(r√L)) )`,  valid only when `r√L ≤ (aμρ/(2²⁰(d+2)))⁴`.

Here `n` is the number of negatives (the reference is repeated `n` times), `L` is the data scale, `μ ≤ 1/10` is the relative defect strength, `a ≤ 1/16` is the overlap of the defect with the DC direction, `r` is the initial radius, `ρ` is the failure probability, and `d ≥ 3` is the dimension. Because of the radius restriction, `log(1/(r√L)) ≥ 4 log(2²⁰(d+2)/(aμρ))`. The bound therefore always includes a `log(d/(aμρ))` factor and the constant `2⁵⁸`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Elementary one-pass method, same oracle (verified below) | `n+1` deterministic calls → `O(n(1+a/μ)log(1/(r√L)))` | **Worse** in every regime, by a factor of at least `2⁵⁸(1+a/μ)·4log(2²⁰(d+2)/(aμρ))` | None | None: both output an exactly separating weight vector, and the baseline is deterministic | Selected result needs randomness, failure probability `ρ`, a tiny-radius restriction, and the GD-only family |
| Repository single-site logistic GD, `FiniteLogisticTwoTapGradientDescent` (commit `f2d9aff8`, earlier the same day). Applies only when `n = m = 1` | `2⌈2⁵³√d/δ·log(1/r)⌉` → `O((1+1/δ)log(1/(r√L)))`, using `a = √(2/d)`, `μ = δ/√(2d)` | Same GD method, about `√d` fewer passes when `√d ≳ 2⁶` and both radius conditions hold | One site → `n` sites with centered, orthogonal residual clouds | None | Needs `d ≥ 512m` and a much smaller admissible radius |
| Tyurin, ICML 2026 ([arXiv 2512.11587 v2](https://arxiv.org/abs/2512.11587), [PMLR v306](https://proceedings.mlr.press/v306/tyurin26a.html)), Thm 5.2: batch perceptron needs `Ω(d/μ)` steps on two samples (Thm 5.1: noisy quadratic perceptron, `Θ̃(√d/μ)`) | `Ω(d/δ)` necessary for batch perceptron → `O((1+1/δ)log(1/(r√L)))` | Beats a *different fixed method*; it is not a problem-class gain | None | None | The comparison is between two methods, both beaten by row 1 |

**Verification of the one-pass baseline.** Query each index once at `(h,t,w) = (1,0,0)`. The readout part of the returned `direction` is exactly `S(input)`, which gives `Sb = Le` and `−Sbᵢ`. Let `m̄` be the mean of the `Sbᵢ`, and output `(1, 0, Sb − λm̄)`. The residuals `zᵢ` are orthogonal to `span{e,u} ∋ m̄`. The reference margin is therefore `L²(1 − λ(1+μa))`, and every negative margin is `L²(λ((1+μa)² + μ²β²) − (1+μa))`, where `β = √(1−a²)`. Any `λ` strictly between `(1+μa)/((1+μa)² + μ²β²)` and `1/(1+μa)` works. This interval is nonempty because `μβ > 0`, and it can be computed from the replies. The companion note itself also reports that two steps of linear logistic GD separate this class.

**Reduction check and proof ancestry.** No standard reduction gives the GD trajectory bound. The growth-cone, sigmoid-secant dispersion control, and crossing/overshoot arguments are new for this model as far as I found. Tyurin's Thm 2.1 (large-norm limit to a quadratic perceptron) motivates the model but supplies no small-initialization or finite-step bound. The problem class itself is solved trivially, so these arguments do not yield an optimization improvement.

**Search coverage (2026-11-25).** I searched arXiv, PMLR/ICML 2026, and general web sources on Tyurin's GD-as-perceptron line and on small-initialization logistic training of linear CNNs. I read Tyurin v2 Thms 2.1, 5.1 and 5.2 (via a fetch summary); Section 6 and the conclusion were not read. I did not check Kumar–Haupt beyond the note's citation. The note's claim that the old step needs `Ω(√d/δ)` passes is analytic and not machine-checked; I did not verify it. The note's "beats perceptron" framing omits the trivial baseline that both methods lose to. No build or axiom audit was run.

## Conclusion

**No: as a method for this data class, the result is beaten by a trivial `n+1`-call procedure.** On this class, the same margin-and-gradient oracle evaluated at filter `(1,0)` returns the samples' sum features. One pass followed by a closed-form linear combination gives an exact deterministic separator:

| Method | Oracle calls |
|---|---|
| One pass + closed-form readout | `n+1` |
| This result (prob. `1−ρ`) | `O(n(1+a/μ)log(1/(r√L)))`, with `log(1/(r√L)) ≳ log(d/(aμρ))` |

The selected bound is never better. The companion note itself also shows that linear logistic GD separates in two steps.

The genuine content is method-specific. It gives a finite-step, small-random-initialization analysis of joint two-tap logistic GD on multi-site defect clouds. In the one-site case it improves the repository's earlier GD bound by about `√d`, and it beats the batch perceptron's `Ω(d/δ)` (Tyurin, Thm 5.2). These are comparisons among artificially fixed methods, not with the strongest applicable algorithm. The setup's exact orthogonality and the common positive reference also lack independent motivation.

What can be claimed is a new trajectory analysis of logistic GD for this bilinear model. It shows no complexity, scope, or oracle advantage for the classification problem.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
