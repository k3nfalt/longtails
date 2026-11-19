# Novelty assessment: CorruptedFirstOrderLowerBound

[`result`](../../LongTails/Theorems/CorruptedFirstOrderLowerBound.lean) proves the following ([setup](../../LongTails/Setups/HighDimensionalCorruptedFirstOrderNonconvex.lean), [base setup](../../LongTails/Setups/CorruptedFirstOrderNonconvex.lean), [adversary](../../LongTails/Proofs/CorruptedFirstOrderLowerBound.lean)). Take any randomized algorithm with joint value-and-gradient queries anywhere in ℝ^d, and any budget N ≤ k + ⌊T/2^25⌋. Then some L-smooth f with f(x₀) − inf f ≤ Δ, together with an oracle that corrupts at most k replies, makes the outer probability of ‖∇f(output)‖ > ε exceed 1/4. The theorem requires T ≥ 2^26 and d ≥ 2^32(1+⌊T/2^25⌋)^4.

**Necessary budget:** Ω(k + LΔ/ε²) calls. Here L is the gradient-Lipschitz constant, Δ the initial gap, ε the gradient-norm tolerance, k the number of corrupted replies, d the dimension, and T = LΔ/ε². The theorem needs LΔ/ε² ≥ 2^26 and d ≳ (LΔ/ε²)^4.

**Hard instance.** The first min(N,k) replies are (0,0) ([delay oracle](../../LongTails/Proofs/CorruptedFirstOrderDelay.lean)). These replies count as corruptions and carry no information. The remaining N−k replies come from the repository's existing randomized smooth hidden chain, and the returned point is treated as one extra query.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon–Duchi–Hinder–Sidford, *Lower bounds for finding stationary points I*, [arXiv 1710.11606 v3 (15 Aug 2019)](https://arxiv.org/abs/1710.11606v3), Math. Program. 184 (2020), **Theorem 2** (randomized). Special case k = 0 only. | Ω(LΔ/ε²) for randomized methods with d ≳ T² log T → Ω(k + LΔ/ε²) | The additive k is new only in this model. It matters when k ≫ LΔ/ε², but it is the trivial "k uninformative replies" term: max{k, cT} ≥ (k + cT)/2. | Clean oracle → oracle with ≤ k adversarial replies. The clean class is the k = 0 sub-case, so the classes are nested. | None. Their criterion (every iterate up to t fails) is at least as strong as failure of the returned point. | Dimension (LΔ/ε²)^4 instead of T² log T. Constant 2^−25. Needs T ≥ 2^26. Their oracle gives all derivatives (stronger), while this one gives value and gradient only. Outer probability covers nonmeasurable algorithm maps, which is a formalization detail. |
| Same paper, **Theorem 1** (deterministic/zero-respecting, d = 1 + 2c₀T). Special case: k = 0 and deterministic algorithms. | Ω(LΔ/ε²) with linear dimension → Ω(k + LΔ/ε²) | Same as above. Adding the delay prefix to it gives Ω(k + LΔ/ε²) for deterministic methods in linear dimension. | As above | None | This result covers randomized algorithms, but pays quartic dimension for that. |

**Standard-reduction check.** The result follows by composition. Run Carmon et al.'s hard instance after k zero replies. Any method that succeeds with N calls then simulates a clean method using N − k calls plus one output query. The note itself states this reduction. Proof ancestry is Carmon et al.'s randomized chain, here in the repository's AbcHard/CorruptedFirstOrderChain formalization. The only new ingredient is the delay prefix, and it is elementary.

**Search coverage.** On 2026-11-19 I searched arXiv and general web sources for lower bounds with adversarially corrupted, faulty or "lying" first-order oracles, and I verified Carmon et al. Theorems 1–2 in the v3 HTML. I found no prior lower bound for exactly this k-reply corruption model. The nearest models I found are different: Byzantine and inexact-gradient models such as [Yin et al. 2018](https://arxiv.org/abs/1806.05358), and corrupted zeroth-order oracles in [Scheinberg–Xie 2025](https://arxiv.org/abs/2511.19411). I did not check the fault-tolerant decision-tree literature beyond the note's citation. Git history dates the result to commit `dc759af6` (2026-11-19). The [companion note](../../LongTails/Theorems/CorruptedFirstOrderLowerBound.md) agrees with the Lean statement, and it correctly calls the delay elementary.

**Conclusion**

**No: this lower bound gives no new complexity insight; it is the standard composition of a trivial term with the classical clean lower bound.**

Carmon–Duchi–Hinder–Sidford (Theorem 2) already prove that finding an ε-stationary point of an L-smooth function needs Ω(LΔ/ε²) queries, even for randomized methods with access to all derivatives. Separately, if an adversary may corrupt k replies, then k answers equal to zero reveal nothing. Putting the two together gives

  necessary calls ≥ k + c·LΔ/ε² (this theorem) ≍ max{k, Ω(LΔ/ε²)} (immediate from prior work).

The value of this theorem is as a converse to the paired [upper bound](../../LongTails/Theorems/CorruptedFirstOrderDescent.lean), which uses ⌈16LΔ/ε²⌉ + 5k + 4 calls. Together they show that O(k + LΔ/ε²) is the right order, within factors 5 in k and 2^29 in LΔ/ε², in the regime LΔ/ε² ≥ 2^26, d ≳ (LΔ/ε²)^4. Any substantive novelty in the pair lies in that additive upper bound, not here. The lower bound is also weaker than the classical one in dimension: it needs quartic rather than T² log T dimension.

What can be claimed is a formalized, matching converse for this corruption model. I found no prior statement of it for this exact model, but the argument is a direct reduction to Carmon et al.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
