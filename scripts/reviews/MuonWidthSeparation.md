# MuonWidthSeparation: novelty assessment

The [theorem](../../LongTails/Theorems/MuonWidthSeparation.lean) runs momentum-free batched Muon ([algorithm](../../LongTails/Algorithms/BatchedDirection.lean), `muon`) with η = ε/(2L), B = ⌈16s²/ε²⌉+1 and a uniformly random output among T+1 = ⌈8LΔ/ε²⌉+1 iterates, and proves 𝔼‖∇f(X̂)‖_* ≤ ε. The [setup](../../LongTails/Setups/ScheduledMomentumComparison.lean)'s success predicate also contains two width-dependent lower bounds, `SgdMomentumLower` and `NsgdMomentumLower`, for SGD-M and Frobenius-normalized SGD-M. Muon's admissible class and success criterion are those of [BatchedSpectralSmooth](../../LongTails/Setups/BatchedSpectralSmooth.lean).

**Parameters.**
- L: ‖∇f(X)−∇f(Y)‖_* ≤ L‖X−Y‖_op.
- Δ: an upper bound on f(X₀) − inf f.
- s: an upper bound on Σᵢσᵢ, the unbiased IID row-profile noise level.
- ε: the target accuracy in nuclear-norm stationarity.
- r = min(m,n), with r ≥ 2, L > 0, s ≥ 0 and LΔ ≥ 72ε².

**Muon budget (upper bound).**

  N_Muon = O((1 + s²/ε²)(1 + LΔ/ε²)) = O(LΔ/ε² + LΔs²/ε⁴),

with no dependence on r.

**Lower bounds (the claimed new part).** Fix any β ∈ [0,1), any deterministic schedule (η_t), any B ≥ 1 and T, and an EMA-momentum method with uniformly random output. Some admissible instance then forces:
- SGD-M: N ≥ (1−β)(r−1)LΔs/(81ε³);
- NSGD-M: N ≥ (r−1)·min{(1−β)LΔs/(288ε³(2+log(1+s√r/ε))), (1−β)²s²/(24ε²)}.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tao–Yu–Zhang (TYZ), [arXiv 2605.06615](https://arxiv.org/abs/2605.06615) v1 (7 May 2026, preprint), Thm 4. This is the same momentum-free batched Muon. Applicability: one-sided noise 𝔼[NNᵀ] ⪯ Σ², with s = ‖Σ‖_*. | Muon: O(1 + LΔ/ε² + LΔs²/ε⁴) → O(LΔ/ε² + LΔs²/ε⁴) | None: same order. | One-sided covariance → row profile. As shown in the [MuonNoiseSeparation review](MuonNoiseSeparation.md), this is a one-line change to TYZ's proof. | None. Both use a random iterate, with L, Δ, s, ε known. | `valid` adds r ≥ 2 and LΔ ≥ 72ε². IID sampling. |
| Repository [MuonNoiseSeparation](../../LongTails/Theorems/MuonNoiseSeparation.lean) (2026-10-23) and its lower bounds `SeparationLower.sgd_lower_bound`/`nsgd_lower_bound`. Applicability: comparators with β = 0 and a constant η > 0. | Muon: (⌈64s²/ε²⌉+1)(⌈8LΔ/ε²⌉+1) → (⌈16s²/ε²⌉+1)(⌈8LΔ/ε²⌉+1). SGD lower bound: (r−1)LΔs²/(1728ε⁴) → (1−β)(r−1)LΔs/(81ε³) | Muon: a constant factor 4 in the batch only. The lower bound is **weaker by a factor of order s/ε** when s ≫ ε. | Comparator family: β = 0 with constant η → any fixed β with any deterministic (η_t) and any B. | None | The certified gap shrinks. At β = 1−1/r, the SGD-M bound becomes ((r−1)/r)·LΔs/(81ε³), which is width-free. |
| TYZ Thm 3; Jiang–Maladkar–Mokhtari ([COLT 2025, PMLR 291](https://proceedings.mlr.press/v291/jiang25c.html), [arXiv 2406.04592](https://arxiv.org/abs/2406.04592) v3), Thm 4.1. Applicability: vector SGD with a **constant** step and no momentum (TYZ Thm 3 also has B = 1), in ℓ∞-smooth / ℓ₁-stationarity geometry. These embed into the target class through diagonal matrices. | TYZ Thm 3 (inverting its min-iterate rate): order dLΔ/ε² + d‖σ‖₂²LΔ/ε⁴ with d ↔ r (I did not extract JMM's exact rate) → (1−β)·r·LΔs/ε³ | Not comparable. Both are lower bounds on comparators, not oracle-complexity guarantees. | Constant step → arbitrary deterministic schedule, plus momentum and batching. | None | The new bound has a smaller s-exponent and no deterministic term (it is vacuous at s = 0). |

**Width-separation regime.** Up to constants, the SGD-M lower bound exceeds N_Muon only when

  (1−β)(r−1) ≳ s/ε + ε/s.

The separation therefore needs a width larger than s/ε, and it fails when β is tuned to width (1−β ≲ 1/r). The certificate covers only uniform-random output. The companion note says, without a proof that I checked, that last-iterate output with a burst-then-anneal schedule defeats these witnesses.

**Reduction check and proof ancestry.** The Muon bound is TYZ Thm 4 plus the triangle-inequality step for the row profile. The lower bounds do not follow from the constant-step proofs: those rely on a stationary-variance formula that schedules break. The new mechanism is a per-step argument weighted by |η_t|: the flat valleys must travel about Δ/ε, and each step's fresh Gaussian kick on the stiff coordinate pays for that travel. I read the argument in the note and Lean statements but did not audit the proof. Proof ancestry: the "stiff + flat valleys" witness comes from the repository's `SeparationInstance`, and the ℓ₁ lower-bound idea from TYZ and JMM.

**Search coverage.** I searched arXiv, PMLR and the web on 2026-10-30. I read TYZ v1 (main text: Thms 3–5), JMM v3 Thm 4.1 (constant η), and Wang et al. [arXiv 2403.15146](https://arxiv.org/abs/2403.15146), whose "any learning rate" SGDM failure result is for a constant η under (L₀,L₁)-smoothness. Two schedule-robust SGD lower bounds exist in other models; I saw them only in abstracts or snippets, and neither covers spectral stationarity:
- Jin–Liang–Zou, [arXiv 2603.03099](https://arxiv.org/abs/2603.03099): high-probability confidence dependence;
- [arXiv 2603.26554](https://arxiv.org/abs/2603.26554): associative-memory capacity.

I found no prior schedule-robust lower bound for SGD-M or NSGD-M in this class; that absence does not prove priority. The result was introduced in commit caa95ae (2026-10-30). The note's claim that the upper bound is not new agrees with my reading.

**Conclusion**

**No new oracle-complexity guarantee: Muon's bound is known, and the new content is a method-specific lower bound for Euclidean momentum methods.**

The convergence guarantee is TYZ Thm 4, a May 2026 preprint, restated with explicit constants for the same algorithm, output and accuracy criterion. Its width-free O(LΔ/ε² + LΔs²/ε⁴) budget does not improve. Even the batch constant only tightens the repository's own earlier copy, from 64s²/ε² to 16s²/ε².

The new part strengthens the comparator lower bounds, so that schedules and momentum can no longer evade the separation:

| Comparator family (needed calls) | Constant step, β = 0 (prior) | Any deterministic schedule, fixed β (new) |
|---|---|---|
| SGD | (r−1)LΔs²/ε⁴ | (1−β)(r−1)LΔs/ε³ |

This is a real extension of the comparator family. It costs one factor of s/ε, beats Muon only when (1−β)r ≳ s/ε + ε/s, holds only for uniform-random output, and vanishes when β = 1−1/r. I found no earlier schedule-robust version in this class, but the search cannot establish priority.

What can be claimed is a formal restatement of a known Muon upper bound plus a modest new negative result for scheduled, fixed-momentum Euclidean methods.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
