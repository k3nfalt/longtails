# Kernel-size-k convolutional QPA on many-sample data: novelty assessment

[`result`](../../LongTails/Theorems/KernelConvolutionalPerceptronAcceleration.lean) proves the following. Take the cyclic non-batch quadratic perceptron (QPA) on Tyurin's convolutional model `m(b;c,v)=⟨Σ_{j<k} c_j P^j b, v⟩`, with no injected noise, the identity filter `c₀=e₁`, `v₀=0`, and step `η=κ/(16√(k/2)R)`. For every dataset in the [setup](../../LongTails/Setups/KernelConvolutionalPerceptron.lean), its last iterate ([algorithm](../../LongTails/Algorithms/KernelConvolutionalPerceptron.lean)) deterministically separates all `N` samples within the budget below.

**Complexity.** The setup has `N=n+1` samples `D_i=(α_i/√2)e+μu_i`, with `e=1/√d`, `g≤|α_i|≤R`, `u_i⊥e` and `‖u_i‖≤1/√k`. There is a unit `w` with `⟨w,highPass_k u_i⟩≥κ`, where `0<κ≤1` and `k≥2`. The oracle returns the exact margin and gradient for one sample. The proved budget is

`N·⌈2·10⁵(R/g)²κ⁻³ log(128kR²/(κμ)²)⌉ = O(N(R/g)²κ⁻³ log(kR/(κμ)))` margin/gradient calls,

valid when `μ²(R/g)⁴log²(…) ≤ kκ⁶R²/10¹³`. The normalisation forces `κ≤2√2/√k`, so the budget is at least of order `N k^{3/2}(R/g)² log(…)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587) (21 May 2026), [ICML 2026, PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html), Thm 5.1. Restricted to `k=2`, `N=2`, dataset (5). | `Õ(√d/μ)` steps w.p. `1−ρ` (unnormalised `b=1_d`) → `O(N(R/g)²κ⁻³log(kR/(κμ)))` | Not comparable: dataset (5) has a pure reference `u₁=0`, so `κ=0` and it is excluded here | Classes are incomparable. Previous: one two-sample instance at `k=2`. Now: `k≥2`, any `N`, either label sign, arbitrary residual geometry | Random start, injected Gaussian noise, high probability → identity start, no noise, deterministic | Every sample needs residual margin `κ>0`. The proof needs a step tuned to `κ`, and the bound has the `κ⁻³` and `2·10⁵` factors |
| Repository [ClusteredConvolutionalPerceptronAcceleration](../../LongTails/Theorems/ClusteredConvolutionalPerceptronAcceleration.lean), added 24 Oct 2026 and unpublished. Restricted to `k=2` and the cap `‖u_i−u⋆‖≤κ/64`. | `N(128(R/g)²log(16R²/μ²)+3)` → `O(N(R/g)²κ⁻³log(R/(κμ)))` on its instances (verified embedding `ofClustered`, same κ) | Worse: about `1.5·10³κ⁻³` times larger on the overlap | Residual cap → none. Unaligned, negatively correlated, growing-rank residuals become covered (formal instance for every `k`) | Start that depends on κ → identity start | The step depends on κ. The contrast condition is more restrictive |
| Fixed high-pass filter plus readout perceptron in the **same model and oracle**. Novikoff (1962) bound, derived in this review. | `N(8/(kκ²)+1)` → `O(N(R/g)²κ⁻³log(kR/(κμ)))` | Worse in every admissible regime, since `log(…) ≥ log 256` | None | None. Both are deterministic with a last-iterate certificate | The selected method is the QPA. This baseline only updates the readout. |
| Read the data, then solve offline (by LP) | `N` → as above | Worse by the full factor `(R/g)²κ⁻³log(…)` | None | None | The selected result is about one particular method |

**Reduction check.** Take the filter `c^H` with `c₀=s(1−1/k)`, `c_j=−s/k` and `s=(1−1/k)^{-1/2}`. It has unit norm and gives `response(c^H,b)=highPass_k b`. Because `Pe=e`, the readout gradient at `(c^H,v)` is `μ·highPass_k u_i`, which has norm at most `2√2μ/√k` and margin at least `μκ` against `w`. A cyclic perceptron that updates only the readout therefore makes at most `8/(kκ²)` mistakes, so `N(8/(kκ²)+1)` calls suffice and `μ` drops out. At the identity start the readout gradient is `D_i` itself, so `N` calls reveal the whole dataset. Separability is guaranteed: `v=highPass_kᵀw` gives margin at least `μκ`. The problem class is therefore trivial in oracle terms, and the content is purely method-specific.

That method-specific content is a decomposition `c=(a/√k)1+t`. Under it the background pair `(a,⟨v,e⟩)` follows the `k=2` dynamics, the high-pass taps `t` stay essentially frozen, and a hybrid multiplicative/additive potential handles Phase 2. The proof ancestry is Tyurin's QPA reduction (Thm 2.1) and Novikoff-type potentials; no later analysis supersedes them. The companion note itself calls the `k>2` answer "deflationary" (the extra taps are not learned). The note's `Ω(1/μ)` comparison is a lower bound for the linear-model perceptron, proved only on a `k=2` family. The proved QPA bound beats it only when `μ ≲ κ³(g/R)²/(10⁶N log(…))`.

**Search coverage (2 Nov 2026 UTC).** I read Tyurin v2 at theorem level (Thms 5.1–5.2, Prop. 6.1, Section 6). I also searched arXiv, ICML 2026 and general web sources, and queried Semantic Scholar, which lists no citations of arXiv:2512.11587. NeurIPS 2026 proceedings were not checked at full-text level. The note's citations to Tyurin are accurate: Section 6 lists larger kernels as an open direction. The result was introduced in commit `fc1475f0` (2 Nov 2026).

## Conclusion

**No optimization advantage is established; the possible novelty is an analysis of one particular method, the identity-started QPA, for kernel sizes k ≥ 2.**

The strongest relevant baseline uses the same convolutional model and the same oracle: fix the high-pass filter, which the model can represent exactly, and run the ordinary perceptron on the readout.

| Method | Calls to separate |
|---|---|
| Fixed high-pass filter + perceptron | `N(8/(kκ²)+1)` |
| This QPA theorem | `O(N(R/g)²κ⁻³ log(kR/(κμ)))` |

The selected bound is worse in every admissible regime. Simply reading the data (`N` calls) is better still.

Compared with prior work, the theorem is the first finite-time QPA guarantee for `k>2`, which Tyurin's ICML 2026 paper lists as open. Within this repository, its `k=2` case also removes the residual cap and the κ-dependent start that the clustered result needed. The cost is a `κ⁻³` factor, and Tyurin's own dataset (5) is not covered. The mechanism shows that the extra taps are frozen to leading order, so the kernel-size extension adds little beyond the existing `k=2` dynamics. The "acceleration" is certified only against the linear-model perceptron, and only for extremely small `μ`.

No published `k>2` QPA analysis was found, so historical priority looks plausible but unconfirmed. The claimable contribution is a new convergence proof for the convolutional QPA with any kernel size on a broader many-sample class. It is not a better guarantee for separating these datasets.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
