# Novelty assessment: `BiasedNoiseSgdUpperBound`

The [theorem](../../LongTails/Theorems/BiasedNoiseSgdUpperBound.lean) proves the following for constant-step SGD ([algorithm](../../LongTails/Algorithms/AbcSgd.lean), `sampledSgd`) with step `γ = 1/max{L(1+M), 4Lσ²/((1−m)ε²)}`, outputting a uniformly random iterate from `{x₀,…,x_K}`. On every `L`-smooth `f` bounded below on a separable Hilbert space, with an IID oracle satisfying the Ajalloeian–Stich bias/noise bounds ([setup](../../LongTails/Setups/BiasedNoiseNonconvex.lean)), the guarantee is `E‖∇f(x̂)‖ ≤ ε` within the stated budget. It requires `0 ≤ m < 1` and `16ζ² ≤ (1−m)ε²`.

**Complexity (oracle calls).** The Lean budget is `⌈16LΔ(1+M+σ²/((1−m)ε²))/((1−m)ε²)⌉ + 1`, which is

  `O( 1 + LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴) )`.

Here `L` is the gradient-Lipschitz constant and `Δ ≥ f(x₀) − inf f`. The bias satisfies `‖E g − ∇f‖² ≤ m‖∇f‖² + ζ²`, and the noise satisfies `E‖g − E g‖² ≤ M‖E g‖² + σ²`. `ε` is the target expected gradient norm. `ζ` enters only through the floor restriction `ζ² ≤ (1−m)ε²/16`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ajalloeian–Stich, [arXiv:2008.00051](https://arxiv.org/abs/2008.00051) (v1 Jul 2020, v2 May 2021; ICML 2020 workshop), Lemma 3 + Theorem 4: same SGD, same Assumptions 1, 3, 4 | Their accuracy parameter is the squared gradient norm, so substitute `ε ↦ ε²`. Their `γ = min{1/((M+1)L), (ε²(1−m)+ζ²)/(2Lσ²)}` is admissible, and `ζ² ≤ (1−m)ε²/16` keeps the floor `ζ²/(1−m)` below `ε²`. This gives `O(LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴))` for `E‖∇f(x_out)‖² ≤ ε²` → `O(1 + LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴))` | None: same order. The added `1` is the counted extra call. | None. The class and oracle bounds are identical (the note copies Assumptions 3–4). | None. Same uniform-iterate output. Jensen turns their `E‖∇f‖² ≤ ε²` into `E‖∇f‖ ≤ ε`. Both need `L,m,M,σ,Δ,ε` for tuning. | The floor condition is a slightly stricter `16ζ² ≤ (1−m)ε²`. Explicit constants (16) replace AS's O-constants. IID sampling and joint measurability are made explicit. |
| Demidovich et al., [NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/hash/484d254ff80e99d543159440a06db0de-Abstract.html), Theorem 3 with the BND→Biased-ABC map (Table 1; Table 4 row) | Stated as `O(LΔ[(M+1)(m+1)/((1−m)²ε²) + ((M+1)ζ²+σ²)/((1−m)²ε⁴)])` → `O(1 + LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴))` | Better by a factor of `1/(1−m)` in the first term, and the `(M+1)ζ²` term is removed. This gain is over the generic-framework specialization, not over AS. | None | None (their criterion is min-iterate `E‖∇f‖²`) | None relative to this weaker row. The table row was taken as the paper states it and was not re-derived. |
| Repository [AbcNoiseSgdUpperBound](../../LongTails/Theorems/AbcNoiseSgdUpperBound.lean) (Khaled–Richtárik Cor. 1), applicable only at `m = ζ = 0` | At `m=ζ=0` the AS noise model is ABC with `A=0, B=M+1, C=σ²`, giving `O(1 + LΔ(1+M)/ε² + LΔσ²/ε⁴)` → identical | None: same order on the overlap | `m=ζ=0` (unbiased) → relative bias `m<1` with additive bias `ζ` | None | None |

**Reduction check.** The result is exactly AS Lemma 3 with their Theorem 4 tuning, rescaled `ε ↦ ε²` and passed through Jensen. The Lean one-step bound (`one_step_biased`) is AS Lemma 2. No new mechanism is involved. At `m=M=ζ=0`, the `σ²` term matches the Arjevani et al. ([arXiv:1912.02365](https://arxiv.org/abs/1912.02365)) lower bound for bounded-variance oracles. The companion [BiasedNoiseLowerBound](../../LongTails/Theorems/BiasedNoiseLowerBound.lean) claims the full term-by-term lower bound. I did not verify that lower bound here, and it is a separate result.

**Search coverage.** On 2026-11-26 I read AS v2 (HTML: assumptions, Lemmas 2–3, Theorem 4, Remark 5) and Demidovich et al. (HTML: Assumption 9, Theorem 3, Tables 1 and 4; appendices not read). I also searched for later biased-SGD nonconvex upper bounds and found none that improves this rate. The companion note's novelty statement ("no algorithmic novelty"; the rate is AS Theorem 4) agrees with this assessment.

**Conclusion**

**No: this is a formalization of a known guarantee, not a new complexity bound or setup.**

The strongest baseline is Ajalloeian–Stich (2020/2021), Theorem 4. It analyzes the same SGD on the same smooth nonconvex class, with the same `(m,ζ²)` bias and `(M,σ²)` noise conditions and the same uniformly sampled output. After rescaling their accuracy to the squared norm `ε²`, both bounds are

  `O( LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴) )`

calls, up to universal constants and one extra counted call.

No regime gives a gain, and the selected result has no information or output advantage. Its step size and horizon need the same parameters, and the `E‖∇f‖ ≤ ε` criterion follows from AS's `E‖∇f‖² ≤ ε²` by Jensen. The improvement over the generic Biased-ABC specialization of Demidovich et al. is only relative to a weaker framework bound; AS already contains it.

What is established is a machine-checked proof with explicit constants (16 and `+1`). Any novelty of the pair lies in the companion lower bound, which this report does not assess.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
