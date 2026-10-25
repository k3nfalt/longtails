# Novelty assessment: ClusteredConvolutionalPerceptronAcceleration

[`result`](../../LongTails/Theorems/ClusteredConvolutionalPerceptronAcceleration.lean) proves a deterministic, last-iterate guarantee. Noiseless, non-batch, cyclic quadratic-perceptron updates ([algorithm](../../LongTails/Algorithms/ClusteredConvolutionalPerceptron.lean)) use step `η = 1/(4R)`, filter start `((κ/8+1)/√2, (κ/8−1)/√2)`, and readout `0`. They strictly separate every signed example of the [setup](../../LongTails/Setups/ClusteredConvolutionalPerceptron.lean). The setup's examples are `Dᵢ = (αᵢ/√2)e + μuᵢ`, with `g ≤ |αᵢ| ≤ R` and centered `uᵢ` lying in a `κ/64`-ball around an unknown center `u⋆`. That center satisfies `‖u⋆‖ ≤ 1/2` and `‖(u⋆−Pu⋆)/√2‖ ≥ 2κ`, with `κ ≤ 1/4`.

**Proved complexity.** The model is the two-tap cyclic convolution `w₁⟨D,v⟩+w₂⟨PD,v⟩`. The parameters are:

- `N` is the number of examples.
- `g` and `R` bound the background coefficients `|αᵢ|`.
- `μ` is the residual contrast.
- `κ` is the derivative margin.

The budget counts exact margin-and-gradient oracle calls:

`N(⌈128(R/g)² log(16R²/μ²)⌉ + 3) = O(N (R/g)² log(R/μ))`.

This requires `μ ≤ κg⁴/(4096R³)`, and then `log(R/μ) ≥ log 4096`. The update uses `κ` and `R`; the budget uses `g`, `R` and `μ`. For `d = 1` the setup admits no instances, because `u − Pu = 0` there.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| One-query direct method, checked here. Query `((1,0),0)`: the readout gradient is `D₀`. Output `((1,0), D₀ − ⟨D₀,e⟩e) = ((1,0), μu₀)` | `1` → `O(N(R/g)² log(R/μ))` | **Worse** by a factor of order `N(R/g)² log(R/μ)` for every admissible instance | None. The baseline needs no contrast restriction and no `κ`, `g`, `R`, `μ`. | None. Both give an exact, deterministic strict separator. | None in the baseline's favour. Its memory is one vector, like the selected method's. |
| Repository [ManySampleConvolutionalPerceptronAcceleration](../../LongTails/Theorems/ManySampleConvolutionalPerceptronAcceleration.lean). **Incomparable class:** it requires a pure reference and derivative-separable defects. | `O((R/g)⁴ log²(R/μ)(N + (R/g) log(R/μ))/κ²)` → the bound above | Method-level only. The classes are not nested, so no common instance class is verified. | The reference example is removed and the derivative separator `⟨rᵢ,s⟩ ≥ κ` is replaced by a cap around a center. Neither class contains the other. | The directed kick is removed, giving an unmodified non-batch QPA update. Both use a fixed start. | The cap `‖uᵢ−u⋆‖ ≤ κ/64` is a new restriction. |
| Tyurin, [ICML 2026](https://icml.cc/virtual/2026/poster/66473) ([arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587), 21 May 2026), Thm 5.1. **Not applicable:** two samples on dataset (5). | `Õ(√d/μ)` w.p. `1−ρ` → not comparable | Not comparable. Dataset (5) contains a pure-background sample (`u = 0`), which the cap excludes because `‖uᵢ‖ ≥ √2κ − κ/64`. | Two fixed samples → `N` interacting clustered residuals | Noisy, high-probability, almost-every start → noiseless, deterministic, one start | A `κ`-dependent initialization and the small-contrast regime |

**Baseline check.** Each `uᵢ` is centered, and `‖uᵢ−Puᵢ‖ ≥ 2√2κ − κ/32`. Hence `‖u₀‖ ≥ √2κ − κ/64`. Also `‖uᵢ−u₀‖ ≤ κ/32`. The margin is then `⟨Dᵢ, μu₀⟩ = μ²⟨uᵢ,u₀⟩ ≥ μ²‖u₀‖(‖u₀‖−κ/32) > 0` for every `i`. This is stronger than the companion note's `N`-call caching remark.

**Reduction check and proof ancestry.** The problem-class guarantee follows trivially by reading one sample and projecting it orthogonally to the known axis `e`. The new mechanism is method-specific: a history cone, a global quadratic inequality `t² ≥ δ(κ²/2)T²`, and a switching contraction for the background coordinates, all applied to noncommuting cyclic updates. The matched lower bound ([`ClusteredPerceptronLowerBound`](../../LongTails/Proofs/ClusteredPerceptronLowerBound.lean)) says that raw or frozen-filter linear perceptron needs `Ω(1/μ)` calls on an explicit family. That is a method-vs-method contrast. Tyurin supplies the proof ancestry: Thm 2.1 reduces large-norm GD to QPA, but its batch QPA differs from this cyclic one-sample rule. Tyurin also supplies the perceptron lower-bound template (Thm 5.2).

**Search coverage (24 Oct 2026 UTC).** I searched arXiv, the ICML 2026 listing and the general web. I read Tyurin v2's theorem statements: Thms 2.1, 4.2, 5.1 and 5.2. Section 6 only extends to larger kernels and more layers, and gives no many-sample rates. I found no follow-up analysing many-sample or clustered QPA; arXiv:2610.23007 and 2608.04382 are unrelated in scope. I did not read the appendices beyond the first half of the HTML or the NeurIPS 2026 "weak alignment" paper, and I did not verify the note's other citations at theorem level. The companion note concedes that no oracle-optimality claim is made. However, it understates the gap: it cites `N` calls, while the actual baseline cost is 1.

## Conclusion

**No: as a way to solve this classification problem, the theorem is beaten by a one-call method.** On this data class, a single exact oracle query returns one example. Removing that example's all-ones component already gives a strict separator for every example, with no parameter knowledge or small-contrast condition:

| Method | Oracle calls |
|---|---|
| Query once, project out `e` | `1` |
| This result | `O(N (R/g)² log(R/μ))`, only when `μ ≤ κg⁴/(4096R³)` |

What the result does establish is a fact about one specific dynamics. Unmodified, noiseless cyclic quadratic-perceptron updates from a fixed `κ`-dependent start separate `N` interacting clustered residuals in `O(N log(1/μ))` calls when `R/g` and `κ` are fixed. Ordinary perceptron, and perceptron with the same frozen filter, provably need `Ω(1/μ)` calls on an explicit growing-rank family. Compared with the repository's many-sample result, it removes the reference example and the directed kick, but it adds a cluster-cap assumption, so the two classes are incomparable.

That method-level contrast extends Tyurin's two-sample acceleration story. My search found no prior many-sample QPA analysis, but that does not establish priority. The setup is also tailored, with a tiny-contrast condition and a cap. What can be claimed is a new deterministic analysis showing that the convolutional perceptron dynamics beat linear perceptron on a specialised clustered family. It is not an improved oracle complexity.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
