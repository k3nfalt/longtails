# Novelty assessment: SublevelPLRobustBatchedGd

[`result`](../../LongTails/Theorems/SublevelPLRobustBatchedGd.lean) proves the following. Take an `L`-smooth `f` on a finite-dimensional space that satisfies `f − inf f ≤ τ‖∇f‖^α` only on `{f ≤ f(x₀)}`, with `1 ≤ α < 2`. Take an IID unbiased gradient oracle with variance at most `σ²` ([setup](../../LongTails/Setups/SublevelPLBoundedVariance.lean)). Then mini-batch gradient descent with step `1/L`, using a majority-vote ("median-of-means") aggregate of sub-batch means ([algorithm](../../LongTails/Algorithms/SublevelRobustGradient.lean)), reaches `E[f(x_K) − inf f] ≤ ε` at its last iterate. The run uses only gradient samples, and the budget is fixed in advance.

**Complexity.** Parameters: `L` is smoothness, `τ, α` are the PŁ constant and exponent, `Δ ≥ f(x₀) − inf f`, `σ²` is the variance and `ε` the target accuracy. Write `c = α/(2−α)` and `D = Lτ^{2/α}ε^{−(2−α)/α}`. The Lean budget `K·m·b` is then

  N = O( (1 + cD) · log(2 + (1+cD)Δ/ε) · [1 + log(2 + (1+cD)Δ/ε) · (cσ²τ^{2/α}ε^{−2/α} + σ²/(Lε))] ).

Assume `D ≥ 1`, which holds throughout the lower bound's range of `ε`. The bound becomes `O(c·D·ℓ + c²·Lσ²τ^{4/α}ε^{−(4−α)/α}·ℓ²)`, where `ℓ = log(2 + cDΔ/ε)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fatkhullin–Etesami–He–Kiyavash, NeurIPS 2022 ([arXiv:2210.01748](https://arxiv.org/abs/2210.01748), Table 1/Cor. 1): SGD under **global** α-PŁ. Masiha–Kiyavash–Thiran (2026, Table 1) list it as the only upper bound for this class, valid "under trajectory containment". | `O(D + Lσ²τ^{4/α}ε^{−(4−α)/α})`, conditional on containment → the bound above | Not comparable as end-to-end bounds: the prior bound is not a theorem on this class. In form the result is worse by `ℓ` (first term), `c·ℓ²` (noise term) and the constant `c` | Global α-PŁ, or an assumed containment of the trajectory → α-PŁ only on `{f ≤ f(x₀)}`, with no containment hypothesis. For α < 2, global α-PŁ plus global smoothness forces `f` to be constant (Masiha et al., Thm 2.1), so the prior theorem covers no non-constant instance here | None (both: expected gap of the last iterate; both need the class parameters) | Not SGD: uses robust batching with `m·b` samples per step; `Δ` enters the logarithms; extra `log²` factors |
| Sadiev et al., ICML 2023 ([arXiv:2302.00999v2](https://arxiv.org/abs/2302.00999), Thm 3.1 Case 2 / Thm E.4): clipped SGD, **α = 2** PŁ and smoothness on a margin set `Q ⊇ {f ≤ f*+2Δ}`. Special-case baseline | With bounded variance: `Õ(L/μ + Lσ²/(μ²ε))`, holding with probability `1−β` → on PŁ-on-`Q` instances with global smoothness (τ = Δ^{1−α/2}(2μ)^{−α/2}, α = 2 − 1/ln(e+Δ/ε)): `O((L/μ + Lσ²/(μ²ε))·log²(e+Δ/ε)·log²(2+LΔ/(με)))` | Worse by polylog factors on the overlap | The classes are incomparable. The result covers α < 2 (e.g. Hölder error-bound geometry, α = 1), which Sadiev does not; Sadiev covers α = 2 exactly, local smoothness, and tails heavier than variance | Worse: expectation instead of high probability. The high-probability bound does not convert to an expectation bound, because the gap on the failure event is not controlled | Global smoothness instead of smoothness on `Q`; finite variance only |
| Masiha–Salehkaleybar–He–Kiyavash–Thiran, AISTATS 2026 ([arXiv:2408.01839v2](https://arxiv.org/abs/2408.01839), Thm 3.2): SARAH | `O(ε^{−2/α})` with constants depending on `τ, σ, L̃, s, R, δ` that are not made explicit → the bound above | Not comparable. The prior method uses a stronger oracle (mean-squared smoothness across query points) and has a better ε exponent | Incomparable: the prior result needs a neighbourhood of an isolated minimizer component, local smoothness, and a start in `𝒰₀` | The prior criterion is conditional on a containment event that holds with probability `1−δ`; the result's expectation is unconditional | The result uses a weaker oracle (bounded variance only) and gives a worse ε exponent |

**Reduction check.** The proof is a short composition of standard tools:
- each step's robust sub-batch aggregate has squared error at most `ν`, except with probability `2^{−m}` (Chebyshev followed by majority boosting, as in Nemirovski–Yudin, Minsker 2015 and Hsu–Sabato 2016);
- a union bound covers all steps;
- on the good event, inexact gradient descent with step `1/L` decreases `f` and stays in the sublevel set while `‖∇f‖² ≥ 8ν`, giving the deterministic recursion of Masiha et al., Prop. 3.2;
- once the gap drops below `ε/2`, smoothness alone bounds the later drift by `Kν/(2L)`;
- the failure event costs at most `Δ·K2^{−m}` in expectation.

The only non-routine observation is the two-phase "hit, then only drift" argument. It removes the need for containment. I found no published theorem that already states this combination. Plain mini-batching with Chebyshev would need batches about `KΔ/ε` times larger (per-step failure `≲ ε/(KΔ)`), so the robust aggregate matters. Proof ancestry: GD on the sublevel set ([Masiha–Kiyavash–Thiran, arXiv:2606.28278v3](https://arxiv.org/abs/2606.28278), Prop. 3.2) and median-of-means confidence boosting.

**Search coverage (2026-11-13).** I searched arXiv, PMLR, NeurIPS and the web for sublevel/local α-PŁ, KŁ, containment, high-probability PL-SGD, clipping and median-of-means. I read the relevant theorem statements of the four papers above. I read the statement of Sadiev's Case 2 rate only in a garbled PDF extraction. I did not check the Sarkar et al. (arXiv:2606.26316), Scaman et al., Louzi, or Weissmann et al. theorems in detail.

Chronology: the result was introduced in commit `ac465015` on 2026-11-13, after the v3 open question of Aug 11, 2026.

The companion note has one discrepancy with the Lean result. It says the theorem answers the open question of Remark 4.2. That remark asks for a self-contained theory for gradient-only **SGD**. The theorem answers the class-level question in Section 5 with a different, batched method, so the SGD question remains open. The note's high-probability variant is not formalized.

Repository overlap: none on this class. `HeavyTailedPLLastIterate` and `GdPL` assume PŁ with α = 2.

## Conclusion

**The rate is unchanged; what is new is an unconditional proof on the sublevel class, obtained with a routine robust-batching argument.**

The strongest relevant baseline is the SGD analysis of Fatkhullin et al., which Masiha–Kiyavash–Thiran list as the only upper bound for this class. That analysis holds only if the trajectory is assumed to stay where α-PŁ holds. With `D = Lτ^{2/α}ε^{−(2−α)/α}` and `c = α/(2−α)`, the two bounds are:

| | Oracle calls | Valid on the sublevel class? |
|---|---|---|
| SGD (conditional) | `D + Lσ²τ^{4/α}ε^{−(4−α)/α}` | Only under assumed containment |
| This result | `c·D·log + c²·Lσ²τ^{4/α}ε^{−(4−α)/α}·log²` | Yes, for every `ε > 0` and α ∈ [1,2) |

This matches the Masiha–Kiyavash–Thiran lower bound up to logarithms and α-dependent constants. In that sense it fills the upper-bound gap for gradient-only methods. It loses polylog factors and gives an expectation guarantee only. In the α = 2 PŁ special case, Sadiev et al. already give comparable high-probability rates.

I found no prior unconditional bound, but a search cannot establish priority. The gain is modest for a concrete reason: the rate is unchanged, and the containment obstacle disappears through a few-line composition of median-of-means boosting, a union bound and an inexact-GD analysis. The theorem also does not settle the stated open question for SGD itself.

What can be claimed is the first checked end-to-end gradient-only upper bound on the sublevel α-PŁ bounded-variance class that matches the lower bound up to logarithms.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
