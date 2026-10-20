# Novelty review: FiniteVarianceMuonHighProbability

[`result`](../../LongTails/Theorems/FiniteVarianceMuonHighProbability.lean) proves this for single-sample exact-polar EMA Muon with a charged batch-validation stage ([`ValidatedMuon`](../../LongTails/Algorithms/ValidatedMuon.lean)), applied to any differentiable, lower-bounded `f` on `m×n` matrices with `‖∇f(X)−∇f(Y)‖_* ≤ L‖X−Y‖_op`, `f(X₀)−inf f ≤ Δ`, and IID unbiased gradients whose noise satisfies a row profile `E‖Nᵀuᵢ‖² ≤ σᵢ²`, `Σσᵢ ≤ s`, in some orthonormal basis ([setup](../../LongTails/Setups/FiniteVarianceSpectralSmooth.lean)): the returned training iterate satisfies `P(‖∇f(X̂)‖_* > ε) ≤ δ`.

**Budget.** The budget is 0 if `2LΔ ≤ ε²`. Otherwise it is

`N = O( (1 + s²/ε²) · [ 1 + LΔ/ε² + √(1 + LΔ/ε²) · log²((1 + s²/ε²)(1 + LΔ/ε²)/δ) ] )`.

This counts all `T + Qbk` training and validation calls. Here `L` is the spectral→nuclear smoothness constant, `Δ` the initial gap, `s` the row-profile noise scale, `ε` the nuclear-norm accuracy, `δ` the failure probability, and `r = min(m,n)`. The algorithm needs `L, Δ, s, ε, δ`. `MuonFamily` enforces the recurrence and selector.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fresh-batch polar NSGD (batch `≍1+s²/ε²`) + Freedman bound on the deficit, using the same selection stage. This is a standard reduction that I checked in outline. The companion note also states it. It is unpublished. | `O((1+s²/ε²)(1+LΔ/ε²+√(LΔ)/ε·log(1/δ)))` + selection → `N` | None: same order when `LΔ/ε² ≥ log⁴(sLΔ/(ε⁴δ))`. Otherwise this result is worse by a factor of up to `log²`. | None | None (training uses batch size 1 instead of a minibatch, but validation is batched) | None beyond the log² overhead |
| [Hübler–Pethick–Sra, 2606.14560v1](https://arxiv.org/html/2606.14560v1), Thm 3.5 (p=2), prior. Expected bound for the same single-sample Muon under `E‖N‖_*² ≤ σ²`. On this class `σ ≤ s` holds. Converted to high probability by Markov's inequality, `log(1/δ)` restarts, and validation. | `O((LΔ/ε² + rLΔs²/ε⁴ + r^{3/2}s³/ε³)·log(1/δ))` → `N` | Better by a factor of about `r·log(1/δ)` in the noise term when `LΔ/ε² ≥ log⁴(…)`. Example: rank-one noise, where `σ = s` exactly. | Nuclear variance → row profile. This is narrower: under nuclear variance alone, the factor `r` is necessary (Thm 3.7 there; [Zhang–Lin 2605.18528](https://arxiv.org/html/2605.18528) Thm 3.1). | Expected averaged → high-probability output, without restarts | The row profile is a stronger noise assumption. Their result covers `p<2` and needs no `s` for its updates. |
| [Kim–Oh, 2601.19156v1](https://arxiv.org/html/2601.19156) Thm 4, prior. Expected bound for Muon (SVD polar) under Frobenius variance `σ_F² ≤ s²`, with the same conversion. | `O((LΔ/ε² + r²s²/ε² + rs²LΔ/ε⁴)·log(1/δ))` → `N` | Better by `r·log(1/δ)` for rank-one profiles. No polynomial gain for isotropic profiles, where `s² ≍ mσ_F²`. | Incomparable noise classes | Same as the previous row | Same as the previous row |
| Euclidean case `m=1`: [Hübler–Fatkhullin–He, AISTATS 2025](https://arxiv.org/html/2410.13849v3), Cor. 5 (minibatch NSGD, high probability), prior | `O(LΔℓ²/ε² + σ²LΔℓ⁴/ε⁴)`, `ℓ = 1+log(1/δ)`, bound on the averaged gradient → `N` with `s = σ` | Gains a factor of `log⁴(1/δ)` when `LΔ/ε² ≥ log⁴(…)`. This gain is reproduced by row 1. | None (their result covers `p ∈ (1,2]`) | Momentum without batching in training. Returns a point rather than bounding an average. | Finite variance only. Parameters must be known. |

**Reduction check and proof ancestry.** The polynomial rate is matched by the fresh-batch reduction in row 1, which uses a bounded nonnegative deficit (`≤ 2√(2L·gap)` on a sublevel set) and Freedman's inequality. The dimension-free noise term comes from a routine Minkowski bound applied row by row, `E‖ΣwₜNₜ‖_* ≤ s‖w‖₂`. What is genuinely new is the delayed-conditioning, stopping, and bootstrap argument that controls the unbounded tracking error of persistent EMA momentum. Proof ancestry:
- The non-Euclidean normalized descent lemma is from [Cutkosky–Mehta 2021](https://arxiv.org/abs/2106.14343), Lemma 1.
- That paper's high-probability Thm 2 is not a competitor. It needs clipping, bounded second moments `E‖∇f(w,z)‖_*² ≤ G²`, and a (2,C)-smooth dual norm, which the nuclear norm is not. Its bound also carries a multiplicative `log(T/δ)`.
- Selection by median-of-means validation is standard.

**Search coverage.** The search was run on 20 Oct 2026 UTC and covered arXiv, ICLR 2026, ICML, AISTATS and NeurIPS sources on Muon, NSGD-M, clipping, sign methods and covariance-envelope noise. The theorem was introduced in commit `71e1228` on 20 Oct 2026.
- Hübler–Fatkhullin–He (v3) explicitly leave high-probability bounds for NSGD-M open. Hübler–Pethick–Sra leave the heavy-tailed high-probability case open.
- No prior unclipped single-sample NSGD-M high-probability bound under finite variance was found.
- Li et al. (ICLR 2026, SGDM) and [ASGO](https://arxiv.org/html/2503.20762v3) (a convex covariance-envelope assumption) were screened only at abstract or assumption level.
- Companion-note mismatch: it calls 2601.19156 "ICLR 2026", but arXiv lists no venue.

**Conclusion**

**No better oracle complexity is established; what is new is a high-probability guarantee for single-sample persistent-momentum Muon itself.** The strongest baseline is plain fresh-batch polar normalized SGD with batch size `≍ 1+s²/ε²`. On the same row-profile class it reaches the same high-probability nuclear-norm guarantee:

| | total oracle calls |
|---|---|
| fresh-batch reduction | `(1+s²/ε²)(LΔ/ε² + √(LΔ)/ε · log(1/δ))` |
| this result | `(1+s²/ε²)(LΔ/ε² + √(LΔ)/ε · log²(sLΔ/(ε⁴δ)))` |

The two are of the same order once `LΔ/ε² ≥ log⁴`; otherwise this result is worse.

Published Muon bounds are about `r·log(1/δ)` worse on rank-one noise profiles. That gap comes from assuming the stronger row-profile noise model and from standard confidence amplification, not from the momentum analysis. The `r` factor is unavoidable under nuclear-norm variance alone.

The real contribution is resolving a published open question. Without clipping, batching or restarts, the EMA momentum carries an unbounded tracking error, and the theorem still achieves logarithmic confidence for it under finite variance alone. This includes Euclidean NSGD-M. The gain is modest because it is method-specific, and its rate and confidence are already available from a simpler minibatch method. Priority looks plausible but rests on a search, not on proof.

What can be claimed: the first (as far as found) finite-variance high-probability analysis of unclipped persistent-EMA Muon/NSGD-M, matching but not improving the class complexity.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
