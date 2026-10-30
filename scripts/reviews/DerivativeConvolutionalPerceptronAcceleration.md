# Novelty assessment: DerivativeConvolutionalPerceptronAcceleration

The [theorem](../../LongTails/Theorems/DerivativeConvolutionalPerceptronAcceleration.lean) proves that the cyclic, simultaneous two-tap quadratic perceptron in [the algorithm module](../../LongTails/Algorithms/DerivativeConvolutionalPerceptron.lean) starts at filter `(√2,0)` with a zero head. With step `η = κ²g²/(2⁴⁰R³)` and the stated deterministic budget, its last iterate strictly separates every sample of the [setup](../../LongTails/Setups/DerivativeConvolutionalPerceptron.lean), using exact margin and gradient oracle calls.

**Proved complexity.** Let `N = samples+1` be the number of samples, `g ≤ |αᵢ| ≤ R` the background bounds, `μ` the contrast scale, and `κ ∈ (0,1]` the common margin of the differenced defects `(uᵢ−Puᵢ)/√2` with norm `‖uᵢ‖ ≤ 1/2`. The proved budget is

  `O( N · κ⁻⁸ (R/g)¹⁰ · (1 + log(R/μ)) )` oracle calls,

restricted to `μ/R ≤ 2⁻⁴⁰⁰ κ²⁰ (g/R)²⁴`. That restriction also forces `log(R/μ) ≥ 277 + 20 log(1/κ) + 24 log(R/g)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Elementary reconstruction (stated in the companion note; checked here): query each sample once at `((√2,0),0)`. The head gradient is `√2Dᵢ`. Then find `v` offline with `⟨Dᵢ−PDᵢ, v⟩ > 0` and output `((1,−1)/√2, v)`. | `N` → `O(Nκ⁻⁸(R/g)¹⁰ log(R/μ))` | Worse by a factor of `Ω(κ⁻⁸(R/g)¹⁰ log(R/μ))` throughout the valid domain | None (same setup) | None. Both output a deterministic strict separator. | The selected method avoids offline computation and storing samples, but the setup counts only oracle calls. |
| Fixed difference-filter perceptron: Rosenblatt/Novikoff mistake bound (Novikoff 1962). Query at `((1,−1)/√2, v)` and update only `v` by the returned head gradient `μrᵢ` after each mistake. | `N(⌊1/(2κ²)⌋+1) = O(N/κ²)` → `O(Nκ⁻⁸(R/g)¹⁰ log(R/μ))` | Worse by `Ω(κ⁻⁶(R/g)¹⁰ log(R/μ))` in every valid regime. The baseline does not depend on `g, R, μ`. | None | None. Both give a last-iterate strict separator. | The baseline uses a filter chosen from the public model structure, not the ordinary start. |
| [Tyurin, ICML 2026 (PMLR 306)](https://proceedings.mlr.press/v306/tyurin26a.html); [arXiv v2, 21 May 2026](https://arxiv.org/abs/2512.11587v2), Thm 5.1. **Special case, not covered here:** two-sample dataset (5). | `Θ̃(√d/μ)` steps, with high probability, for a perturbed batch QPA → not comparable | Not comparable: dataset (5) contains the pure-constant sample `1`, which has zero defect and violates the derivative-margin condition | Two specific samples → `N` samples with a common derivative separator. The classes are incomparable, not nested. | Random perturbation and initialization correlation → deterministic run from an explicit ordinary start | Requires a lower background bound and the extreme contrast threshold above |

**Reduction check and proof ancestry.** Both rows above are direct, verified constructions under the same oracle and output criterion, so no reduction is needed to dismiss a problem-class improvement. Because `P` fixes the constant axis, `Dᵢ−PDᵢ = μ(uᵢ−Puᵢ)`. The perceptron therefore sees features `μrᵢ` with norm at most `μ/√2` and margin at least `μκ`, which gives at most `1/(2κ²)` mistakes. What is genuinely new is in the method-specific trajectory analysis: two coupled barriers and energy control that make the unmodified ordinary-start learned-filter dynamics suppress the background in `O(log(R/μ))` passes. By contrast, the companion note's frozen raw-filter perceptron needs `Ω(1/μ)` calls on its growing-rank family. Tyurin's QPA reduction (Thm 2.1) supplies the algorithmic model, not this bound.

**Search coverage.** On 2026-10-30 I checked Tyurin's arXiv v2 (Thms 2.1, 5.1–5.2 and Section 6 via HTML; Section 6 has no many-sample or convolutional convergence theorem) and the PMLR page. I also ran web searches for many-sample, convolutional or quadratic-perceptron acceleration. These searches found no prior many-sample convolutional QPA theorem. That is not proof of priority. The companion note's other citations (Yun et al.; Diederen et al.; Wang et al. 2210.09371; the inaccessible NeurIPS 2026 OpenReview manuscript) were not independently reread. The note's own admission that the budget is not optimal agrees with this assessment. It names the reconstruction baseline but not the stronger `O(N/κ²)` fixed-filter perceptron gap. Within the repository, the result removes the cap assumption of [ClusteredConvolutionalPerceptronAcceleration](../../LongTails/Theorems/ClusteredConvolutionalPerceptronAcceleration.lean) (2026-10-24) and the reference sample and interventions of [ManySampleConvolutionalPerceptronAcceleration](../../LongTails/Theorems/ManySampleConvolutionalPerceptronAcceleration.lean). Those are repository increments, not literature baselines.

## Conclusion

**No: for the stated separation problem the result is strictly worse than elementary methods; it only gives a new analysis of one particular trajectory.**

Under exactly the same exact-margin/gradient oracle and strict-separation output:

| Method | Oracle calls |
|---|---|
| Read each sample once, separate offline | `N` |
| Perceptron with fixed difference filter `(1,−1)/√2` | `O(N/κ²)` |
| This result (ordinary-start learned filter) | `O(Nκ⁻⁸(R/g)¹⁰ log(R/μ))`, only when `μ/R ≤ 2⁻⁴⁰⁰κ²⁰(g/R)²⁴` |

The fixed-filter perceptron wins in every valid regime, by a factor of at least `κ⁻⁶(R/g)¹⁰ log(R/μ)`, and it needs no contrast threshold.

The interesting content is method-specific. Starting from the raw one-tap filter, the coupled quadratic-perceptron updates learn the differencing filter and pay only `log(1/μ)` instead of the frozen raw filter's `Ω(1/μ)`, for arbitrarily many samples without a cap or reference sample. That extends Tyurin's two-sample phenomenon to an incomparable many-sample class. My search found no earlier theorem of this form, but coverage is limited and that establishes neither priority nor an optimization advantage.

What can be claimed is a new deterministic many-sample convergence analysis of the ordinary-start convolutional quadratic perceptron, under a strong sufficient contrast condition. As in the negative examples, this analysis alone gives no complexity, scope or oracle improvement for the problem class.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
