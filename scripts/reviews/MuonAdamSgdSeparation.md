# MuonAdamSgdSeparation: novelty assessment

The [theorem](../../LongTails/Theorems/MuonAdamSgdSeparation.lean) is stated on the [setup](../../LongTails/Setups/SpectralSmoothAdamComparison.lean) and runs batched exact-polar Muon ([algorithm](../../LongTails/Algorithms/BatchedDirection.lean), `muon`). It proves three things on the same class of r×r matrix problems:
- Muon with B = 65, η = ε/(2L) and a uniformly random iterate reaches 𝔼‖∇f(X̂)‖_* ≤ ε.
- Every constant-parameter, bias-corrected Adam needs N ≥ min{√((r−1)/64), ((r−1)LΔ/(4096ε²))^{1/3}} calls on some instance.
- Every constant-step batched SGD needs N ≥ (r−1)LΔ/(1728ε²).

Here Adam ranges over all η > 0, τ ≥ 0, B ≥ 1 and β₁² ≤ β₂ < 1, and both Adam and SGD return a uniformly random iterate.

**Complexity.** The Muon budget is

  N = 65(⌈8LΔ/ε²⌉ + 1) = O(LΔ/ε²), valid for r ≥ 4 and LΔ ≥ 128ε².

The parameters mean the following:
- L: nuclear/spectral smoothness, ‖∇f(X)−∇f(Y)‖_* ≤ L‖X−Y‖_op.
- Δ: the initial gap, f(X₀) − inf f.
- ε: the target accuracy. It also equals the noise level s, the bound on Σσᵢ in the row-profile condition, under IID unbiased sampling.
- r: the matrix dimension.

The bound does not depend on r.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tao–Yu–Zhang, [arXiv 2605.06615](https://arxiv.org/abs/2605.06615) v1 (7 May 2026, preprint), Thm 4: the same batched momentum-free Muon. It assumes one-sided noise with s = ‖Σ‖_*. | O(1 + LΔ/ε² + LΔs²/ε⁴), which at s = ε is O(LΔ/ε²) → O(LΔ/ε²) | None: same order. | One-sided covariance → row profile. This mild relaxation was already in the repository's [MuonNoiseSeparation](MuonNoiseSeparation.md); see that review. | None. Both use a uniform random iterate. | The new result fixes s = ε and requires square matrices with r ≥ 4. |
| Repository: [MuonNoiseSeparation](../../LongTails/Theorems/MuonNoiseSeparation.lean) together with `SeparationLower.sgd_lower_bound` (added 2026-10-23). Same class, same Muon, and SGD lower bound (r−1)LΔs²/ε⁴ ≤ 1728·N. | Muon O((1+s²/ε²)(1+LΔ/ε²)) and SGD Ω(rLΔ/ε²) at s = ε → identical, now reused | None. | None. | None. | The Muon-vs-SGD separation is reused, not new. |
| Prior Adam-side results. Wang et al., [arXiv 2509.26030](https://arxiv.org/abs/2509.26030) (ICLR 2026), Thm 5.3: one-step worst case for Adam taken as SignGD (β₁ = β₂ = 0). Reddi et al., [ICLR 2018 / arXiv 1904.09237](https://arxiv.org/abs/1904.09237), Thm 3: for every β₁ < √β₂, a 1-D constrained stochastic convex problem on which Adam with α/√t steps does not converge. Applicability: neither is a complexity bound on this class. | No complexity lower bound for full Adam in nuclear stationarity → Ω(min{√r, (rLΔ/ε²)^{1/3}}) | Not comparable: this is a new lower bound for one method, not a faster upper bound. | Special case → full two-moment, multistep, batch-uniform Adam on a dense nonlinear matrix instance. | The Adam lower bound covers only uniform-iterate output. | The exponent r^{1/3} is not shown to be tight. It excludes β₁² > β₂, schedules, AdamW, and last or averaged outputs. |

**Strict-separation regime.** Muon beats both lower bounds once r−1 > max{64K², 4096K³/Q, 1728K/Q}, where Q = LΔ/ε² and K = 65(⌈8Q⌉+1). The middle term dominates and is about 5.8·10¹¹Q². At the smallest allowed Q = 128, this needs r ≳ 9.5·10¹⁵. The separation is therefore asymptotic in r and not quantitative at practical sizes.

**Standard-reduction check and proof ancestry.** Two of the three pieces follow from known work:
- The Muon guarantee is TYZ's descent argument with the row-profile noise bound.
- The SGD piece is the existing repository lemma.

The Adam lower bound does not follow by norm conversion, rescaling, or Adam→SignGD reduction. It has to handle τ, β₁, β₂ and B together; for example, a large τ makes Adam behave like scaled SGD.

The proof uses rank-one Rademacher noise along J = uuᵀ and a smoothed valley in the quiet direction P. According to the companion note (I checked only the top-level Lean skeleton), it bounds diagonal/off-diagonal leakage through the full normalized history using |m̂| ≤ t√v̂ from β₁² ≤ β₂. I found no earlier use of this mechanism. The rotation sensitivity it exploits is folklore (e.g., [Maes et al., NeurIPS 2025](https://papers.nips.cc/paper_files/paper/2025/file/a6ffe4ec7aaa6e7e7d5bd28e14827d3a-Paper-Conference.pdf)).

I did not run `./build.sh` or the comparator, so formal correctness was not re-verified.

**Search coverage.** I searched arXiv, the web, and the NeurIPS/ICLR pages on 2026-10-25, and checked these sources:
- TYZ (abstract and the prior review);
- Wang et al. (Thms 5.3–5.4, HTML);
- Reddi et al. (Thm 3, PDF text);
- Zhang–Lin [arXiv 2605.18528](https://arxiv.org/abs/2605.18528) v4, abstract only. Its general Ω(min{m,n}·…) heavy-tail lower bound uses a different noise scaling and no Adam;
- Sun–Li–Lin [arXiv 2609.24522](https://arxiv.org/abs/2609.24522), abstract only. It gives an Adam nuclear-norm upper bound; the note's formula for it is unverified;
- Ma et al. [arXiv 2601.13474](https://arxiv.org/abs/2601.13474) and Wu et al. [arXiv 2608.25990](https://arxiv.org/abs/2608.25990), abstracts only.

I found no prior lower bound for full Adam in this setting. The full texts of Hübler–Pethick–Sra and Ma et al. were not checked. The companion note's claims match the Lean statement, and it correctly disclaims novelty for the Muon and SGD parts.

**Conclusion**

**No problem-class complexity improves; the one new piece is a worst-case lower bound for constant-parameter Adam.**

The Muon side gives no new guarantee. Its O(LΔ/ε²) budget is Tao–Yu–Zhang's Theorem 4 at s = ε, and the SGD lower bound was already in the repository. What is new is a proved impossibility for full bias-corrected Adam: every allowed tuning fails on some admissible instance unless

  N ≥ min{√((r−1)/64), ((r−1)LΔ/(4096ε²))^{1/3}}, compared with Muon's 65(⌈8LΔ/ε²⌉+1).

I found no earlier lower bound covering multistep two-moment Adam. Prior Adam results are either one-step SignGD comparisons or non-convergence examples for specific schedules. That supports priority, but my search was targeted, so it does not prove priority.

The contribution is modest for concrete reasons:
- It is a lower bound for one method, and the r^{1/3} exponent is not shown to be tight.
- It requires constant parameters, β₁² ≤ β₂, and uniform-iterate output.
- The noise is fixed at s = ε.
- Muon provably wins only once r exceeds roughly 10¹⁶ at LΔ/ε² = 128.

What can be claimed is the first formal separation in dimension dependence between batched Muon and every constant-tuned Adam, with Adam needing at least order r^{1/3} calls on this class.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
