# Novelty assessment: ManySampleConvolutionalPerceptronAcceleration

[`result`](../../LongTails/Theorems/ManySampleConvolutionalPerceptronAcceleration.lean) proves that a perturbed, reference-first cyclic quadratic perceptron ([algorithm](../../LongTails/Algorithms/ManySampleConvolutionalPerceptron.lean)) outputs a strictly separating filter/readout pair after the stated number of exact signed-margin/gradient calls. The output is the final iterate, and the guarantee holds deterministically for every admissible dataset in the [setup](../../LongTails/Setups/ManySampleConvolutionalPerceptron.lean).

**Proved complexity.** The model is the length-2 cyclic convolution `a₁⟨b,v⟩+a₂⟨Pb,v⟩`. The data consist of one positive reference `(α₀/√2)e` and `n` negatives `(αᵢ/√2)e+μuᵢ`, where `e` is the normalized all-ones vector. The parameters satisfy `g ≤ αᵢ ≤ R`, `uᵢ ⊥ e`, `‖uᵢ‖ ≤ 1/√2`, and the defects are separable after cyclic differencing with margin `κ ≤ 1`. In the validity regime, the proved budget simplifies to

`O( (R/g)⁴ log²(R/μ) · (n + (R/g) log(R/μ)) / κ² )` oracle calls.

This regime requires `δ(B+1)³ ≤ κ³/2²⁴` and `δ(B+1)² ≤ κ²(g/4R)⁴/2²⁴`, with `δ = μ²/(16R²)` and `B ≈ 128(R/g)² log(16R²/μ²)`. Roughly, `μ/R ≲ 2⁻²² κ^{3/2}(g/R)³ / log^{3/2}(R/μ)` is needed. The updates use `R` and `μ` through the step and kick sizes. The budget also uses `g` and `κ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Reconstruct-then-solve, checked here. At `θ=((1,0),0)` the oracle's readout gradient is the signed sample. After `N=n+1` calls, solve an LP offline for `w` with `⟨bᵢ−Pbᵢ,w⟩<0`. Then take `t=1`, `v=c e+w`, and a small filter mean `a` (see below). | `n+1` → `O((R/g)⁴log²(R/μ)(n+(R/g)log(R/μ))/κ²)` | **Worse** by `(R/g)⁴log²(R/μ)(1+(R/g)log(R/μ)/n)/κ²` in every regime | None. The baseline needs no contrast regime. | None. The baseline needs no knowledge of `g,R,μ,κ` and certifies its output exactly. | The selected method keeps `O(d)` state instead of storing `O(nd)` data. The setup imposes no memory constraint. |
| Tyurin, [ICML 2026, PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html) ([arXiv v2, 21 May 2026](https://arxiv.org/html/2512.11587v2)), Thm 5.1. **Special case:** only dataset (5) with `n=1`, `b₂ = 1+μE₀`. | `Õ(√d/μ)` w.p. `1−ρ` → `O(log³(d/μ))` when `μ ≲ 2⁻²²√d/log^{3/2}(d/μ)` (maps to `R/g≈1`, `κ=1/√2`) | Method-level only: `√d/μ` → polylog for a modified QPA in that regime. Not a problem-class gain (2 calls suffice). | Two fixed points → any `n`, arbitrary derivative-separable centered defects | High probability → deterministic. Almost-every random start → one specific start. | Different method: a deterministic directed kick uses the sign of `a+q` along `e`, instead of tuned Gaussian noise. Also a zero readout, filter `(√2,0)`, and a restarting scan. Needs the small-contrast regime. |
| Repository [TwoSampleQuadraticPerceptronAcceleration](../../LongTails/Theorems/TwoSampleQuadraticPerceptronAcceleration.md) (conv case, `n=1`) | `O(√d/μ·log)` on dataset (5) → `O(log³(d/μ))` in the same regime | Same method-level gain, under the same caveats | `n=1` positive-mean data → many samples. The classes are otherwise incomparable: no pure-reference requirement there. | Cone initializations → one fixed start | Same restrictions as the previous row |

**Admissibility check for the baseline.** Let `t=1` (raw filter difference), `v = (μ/R)e + w` with `w` the centered unit separator, and `a < κ/2`. Then the reference margin is `aα₀μ/R > 0`. Each negative signed margin is at least `μκ − a(μ+μ) > 0`, using `⟨rᵢ,e⟩=0` and `‖pᵢ‖ ≤ 1`. The LP finds such a `w` from the cached data. The companion note states this baseline too and concedes the gap.

**Reduction check and mechanism.** The problem-class guarantee follows from data reconstruction plus offline linear separation (Novikoff/LP; [Wang et al., arXiv:2210.09371](https://arxiv.org/abs/2210.09371) for accelerated arithmetic). The genuinely new ingredient is the coupled, switched many-sample QPA analysis: a sign-contraction potential for `(a,q)`, a finite-prefix bootstrap, and a reference-escape count. Tyurin supplies the GD-as-perceptron reduction and the two-sample QPA template. Tyurin's Thm 2.1 equivalence to GD does not cover the added deterministic kick, so this is not a GD analysis.

**Search coverage (23 Oct 2026).** Sources checked: arXiv/PMLR for Tyurin (theorem statements read from v2 HTML, first half), Wang et al., and general searches on perceptron and linear-convolutional dynamics. No many-sample QPA result was found before or after the result's introduction (commit `37fb450`, 23 Oct 2026). I did not read Yun–Krishnan–Mobahi (ICLR 2021) or the second-order perceptron papers myself. They are not needed for the verdict, because the reconstruction baseline already dominates. Unlike the companion note, I count the polylog gain over Tyurin's QPA bound on dataset (5) as a method-level gain. The note does not mention it.

## Conclusion

**No: as an algorithm for this data class, the result is beaten by a trivial N-call method.** At filter `(1,0)` and zero readout, the exact oracle's readout gradient is the sample itself. Reading every sample once and solving a small LP offline gives a strict separator without any parameter knowledge or contrast restriction:

| Method | Oracle calls |
|---|---|
| Reconstruct + LP | `n+1` |
| This result | `O((R/g)⁴ log²(R/μ)(n+(R/g)log(R/μ))/κ²)` |

The selected bound is never better. At best it comes within `log²(R/μ)` of the baseline, when `R/g` and `κ` are constants and `n ≳ (R/g)log(R/μ)`.

As a statement about quadratic-perceptron dynamics, it is more interesting. It extends Tyurin's two-sample theorem to arbitrary many-sample derivative-separable defects. On Tyurin's own dataset, its bound is `O(log³(d/μ))`, versus `Õ(√d/μ)`, whenever `μ ≲ 2⁻²²√d/log^{3/2}(d/μ)`. However, the algorithm is modified (directed deterministic kick, special initialization, restarting scan), so the result does not analyze Tyurin's GD-equivalent method. The setup is also artificial: it requires a pure positive reference and a stringent small-contrast regime.

What can be claimed is a new finite-time analysis of a perturbed short-filter QPA variant on many samples. It does not give a better way to solve the classification problem. The literature search suggests the analysis is new, but it does not prove priority.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
