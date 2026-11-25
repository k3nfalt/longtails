# Novelty assessment: CyclicLogisticFeatureLearning

[`result`](../../LongTails/Theorems/CyclicLogisticFeatureLearning.lean) proves the following. Take full-batch logistic GD on the two-tap cyclic convolution model `m_i = h₁⟨b_i,v⟩ + h₂⟨Pb_i,v⟩`, started at `h=(1,0), v=0`, with step `η = ρκ/(2¹⁶nL)`, and freeze it at the first pass where every margin is positive. Under the [setup](../../LongTails/Setups/CyclicLogisticFeatureLearning.lean) geometry, the [algorithm](../../LongTails/Algorithms/CyclicLogisticFeatureLearning.lean)'s output then classifies all `n` signed examples with strictly positive margin, deterministically.

**Complexity** (component calls; one call returns one example's margin and parameter gradient):

  `O( n³ log²(2 + n/(μκ)) / (ρ μ κ²) )`

The parameters are as follows. `n` is the number of samples. With `z_i=(b_i+Pb_i)/√2` and `r_i=(b_i−Pb_i)/√2`, the setup assumes `‖z_i‖≤1`, `‖r_i‖≤μ`, a unit `u` with `⟨r_i,u⟩≥μκ`, convex hull of the `z_i` containing a radius-`ρ` ball in their span, and `⟨z_i,r_j⟩=0`. All of `μ,κ,ρ ∈ (0,1]`, and `d` is even. The budget is exactly `n(⌈2²³n²L²/(ρμκ²)⌉+1)`, including the certification pass.

**Reductions available in this oracle** (checked by hand):
- Project `u` onto span{r_i} and normalize, giving `û`. Then `⟨b_i,û⟩ ≥ μκ/√2` while `‖b_i‖ ≤ √2`, so the raw rows have normalized margin at least `μκ/2`.
- A query at `h=(1,0)` returns `b_i` itself. So `n` calls reveal the whole dataset, and linear-model gradients cost one call per example.
- A query at `h=(1,−1)/√2` gives margin `⟨r_i,v⟩` and direction block `r_i`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Novikoff perceptron, run cyclically with the filter fixed at the difference filter `h=(1,−1)/√2` (classical; R=μ, margin μκ) | `n(1+1/κ²)` → `n³L²/(ρμκ²)` | Worse in every regime: the ratio is at least `n²/(ρμ)` | None | None: both outputs are certified strict separators | Uses the public shift structure through a fixed filter. Here GD has to learn the filter. |
| Soheili–Peña smooth perceptron on the normalized raw rows ([SIAM J. Optim. 22 (2012), Thm 1](https://optimization-online.org/wp-content/uploads/2011/09/3170.pdf)): at most `2√log n/ρ(A) − 1` iterations, one full pass each | `n(1+√log n/(μκ))` → `n³L²/(ρμκ²)` | Worse: about a factor `n²/(κρ)` up to logs | None | None | Momentum/smoothing method, not plain GD. It needs no difference filter. |
| Read all `n` examples, then solve the LP offline | `n` → `n³L²/(ρμκ²)` | Worse | None | None | Computation is not counted in the oracle budget. |
| [Tyurin, ICML 2026](https://proceedings.mlr.press/v306/tyurin26a.html) ([arXiv v2, 21 May 2026](https://arxiv.org/html/2512.11587v2)): Thm 2.1 is the `‖w₀‖→∞` perceptron limit; §5 gives `Õ(√d/μ)` vs `Ω(d/μ)` on a prescribed pair | Not comparable: the quadratic perceptron limit, not finite-step GD | Not comparable | Two fixed samples (per the paper's §1.3; the §5 details are unverified) → arbitrary `n`-sample clouds under the new orthogonal geometry | Limiting dynamics → actual finite-step logistic GD iterate | Exact cross-channel orthogonality, even `d`, and `n³` and `ρ⁻¹` factors. |

**Reduction check and new mechanism.** The selected complexity does not follow from a known theorem by substitution. The proof's new ingredient is a finite-step descent and imbalance-telescoping argument for the bilinear model, with nuisance-energy control that keeps the step from scaling with `μ` ([trajectory proof](../../LongTails/Proofs/CyclicLogisticTrajectory.lean)). The perceptron-reduction idea comes from Tyurin (2412.08424; 2512.11587). However, standard first-order linear-feasibility methods already solve this problem class faster.

The same-data linear comparison is a supporting lemma: a delay of more than `d/2²⁰ = Ω(μ⁻²)` steps on one six-row family, for constant-step linear GD from zero. It is not a problem-class lower bound. [Zhang–Wu–Lin–Bartlett (JMLR 27, 2026)](https://arxiv.org/abs/2504.04105) prove an `Ω(1/γ²)` first-order lower bound only with unrestricted `n`, so it does not apply to fixed `n`.

**Search coverage.** I searched on 2026-11-25: Tyurin's papers, the smooth/accelerated perceptron line (Soheili–Peña; [Wang et al., ICLR 2023](https://arxiv.org/abs/2210.09371)), large/adaptive-step logistic GD, and convolutional linear networks ([Gunasekar et al., NeurIPS 2018](https://arxiv.org/abs/1806.00468)). I found no prior finite-step multi-sample analysis of this exact model.

I could not verify the companion note's "Musat and Boumal" attribution: arXiv 2610.26748 surfaced only under a multiclass-logistic title. I also did not verify Tyurin's §5 statements or the Wen–Wen–Teng preprint. In the repository, the closest results are [ManySampleConvolutionalPerceptronAcceleration](ManySampleConvolutionalPerceptronAcceleration.md) and [FiniteScaleConvolutionalSgd](FiniteScaleConvolutionalSgd.md). Both use different setups, and both are rated NO IMPROVEMENT.

The note correctly admits that "an explicitly chosen difference filter, or direct separation after reading the data" can change the comparison. However, it does not show that those baselines are strictly faster.

## Conclusion

**No complexity or problem-class advantage is established; what is new is a finite-step guarantee for this particular GD dynamics.**

On the stated data class, the strongest simple baseline fixes the difference filter and runs the perceptron:

| Method (same oracle, strict separation) | Component calls |
|---|---|
| This theorem: joint-filter logistic GD | `O(n³ log²(2+n/(μκ)) / (ρμκ²))` |
| Difference-filter perceptron | `n(1 + 1/κ²)` |
| Smooth perceptron on raw rows | `O(n(1 + √log n/(μκ)))` |

The baselines win for every admissible `n, μ, κ, ρ`, and they need neither the nuisance-inradius assumption `ρ` nor a learned filter. The theorem's "acceleration" is relative only to constant-step linear logistic GD from zero, and on one hard family it improves `Ω(μ⁻²)` to `O(μ⁻¹ log²(1/μ))` passes. It does not beat accelerated or structure-aware linear methods.

What is established: an explicit finite-step, multi-sample guarantee for genuine logistic GD with a jointly trained two-tap filter. This extends Tyurin's limiting, two-sample perceptron analysis, under a new and rather rigid orthogonality geometry. Priority for that method-specific analysis looks plausible from my search, but the listed sources remain unverified, and the analysis does not by itself make the method a better optimizer for this problem.

The contribution that can be claimed is a new analysis of implicit acceleration in convolutional logistic GD, not an improved oracle complexity.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
