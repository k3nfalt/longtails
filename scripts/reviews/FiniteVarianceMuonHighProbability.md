# Novelty review: FiniteVarianceMuonHighProbability

[`result`](../../LongTails/Theorems/FiniteVarianceMuonHighProbability.lean) proves this for lower-bounded `f` on `m×n` matrices with `‖∇f(X)−∇f(Y)‖_* ≤ L‖X−Y‖_op` ([setup](../../LongTails/Setups/FiniteVarianceSpectralSmooth.lean)), with unbiased IID gradients and row-profile noise `E‖(G−∇f)ᵀuᵢ‖² ≤ σᵢ²`, `Σσᵢ ≤ s`. Plain EMA Muon is run with exact polar steps and one sample per step, followed by random pool selection and batched median-type validation ([algorithm](../../LongTails/Algorithms/ValidatedMuon.lean)). The returned training iterate satisfies `P(‖∇f(X̂)‖_* > ε) ≤ δ`.

**Proved budget.** Here `L` is the spectral-to-nuclear smoothness constant, `Δ ≥ f(X₀) − inf f`, `s` is the row-profile noise scale, and `ε, δ` are the nuclear-norm accuracy and failure probability. The budget is `0` if `2LΔ ≤ ε²`; otherwise it is

`N = O( (1+s²/ε²) · [ 1 + LΔ/ε² + √(1+LΔ/ε²) · log²((1+s²/ε²)(1+LΔ/ε²)/δ) ] )`,

with no dimension factor. The theorem uses `allowedAlgorithm` (`MuonFamily`), which enforces the recurrence and output rule.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Minibatch normalized SGD, [Hübler–Fatkhullin–He, AISTATS 2025](https://proceedings.mlr.press/v258/hubler25a.html), Thm 4 ([arXiv v3](https://arxiv.org/abs/2410.13849)), transferred to polar steps (my reduction, below), batch `b≍1+s²/ε²`, plus the same selection/validation stage | `O((1+s²/ε²)[(1+LΔ/ε²)log(2/δ) + log(2/δ)log(log(2/δ)/δ)])` → `N` | Saves up to a `log(1/δ)` factor only when `√(LΔ/ε²)·log(1/δ) ≳ log²((1+s²/ε²)(1+LΔ/ε²)/δ)`. Worse when `√(1+LΔ/ε²) < log²((1+s²/ε²)(1+LΔ/ε²))` at fixed `δ`, or when `log(1/δ) ≫ LΔ/ε²` (by `√(LΔ/ε²)`). | None | None: both return a validated iterate with the same quantifiers | Selected training uses one sample per step and keeps persistent momentum, but its validation is batched anyway. It is limited to finite variance (`p=2`); Thm 4 needs only a conditional first moment. |
| Persistent Muon (NSD‑M), [Hübler–Pethick–Sra, arXiv 2606.14560v1 (12 Jun 2026)](https://arxiv.org/abs/2606.14560), Thm 3.5; **expected guarantee only** | Expected averaged nuclear gradient: `O(min(m,n)·LΔs²/ε⁴ + …)`, with lower-order terms not extracted → `N` with probability `1−δ` | Not comparable as stated (expectation versus probability). On the row-profile class the leading term loses `min(m,n)`, but that factor comes from their weaker noise class. | Incomparable: their condition is nuclear `p`-th moment `≤ σ^p`, `p∈(1,2]`, which is broader; this result needs a row profile, which implies nuclear variance `≤ s²` | Expectation → `1−δ` probability for the same persistent update. The conclusion of 2606.14560 calls this extension open. | Row profile is stronger, and only `p=2` is covered |
| [Cutkosky–Mehta, NeurIPS 2021](https://arxiv.org/abs/2106.14343), Thm 2/Cor 4; **special case** (2‑smooth dual norm, for example the one-row Euclidean case) | `‖∇F‖ ≤ O(log(T/δ)T^{-1/4})`, i.e. `Õ(ε⁻⁴ log⁴(1/δ))`; constants in `L,Δ,G` not extracted → `N` | Not comparable: it only has a 2‑smooth norm and bounded non-central moments | Their requirements `E‖g‖^p ≤ G^p` (bounded gradients) and clipping → central variance only, with unbounded gradients allowed and no clipping | No-clipping persistent momentum. Their result also covers `p<2`. | Nuclear norm is not 2‑smooth with an `O(1)` constant, so their theorem does not cover the matrix case |

**Reduction check.** In Hübler et al.'s Thm 4 proof (Lemmas 7, 11, 14), only these facts are used: `⟨∇F, d⟩ ≥ ‖∇F‖_* − 2‖g−∇F‖_*`, the unit-norm descent step, and `‖∇F(x_t)‖_* ≤ ‖∇F(x₁)‖_* + L·Σ_{τ<t}η_τ`. All three hold for polar steps in the spectral/nuclear pair, and `‖∇F(x₁)‖_*² ≤ 2LΔ`. The row profile gives `E‖ḡ−∇F‖_* ≤ s/√b`. Their `C_T = Tη²` term makes the `log(1/δ)` multiplicative (Cor 5), which gives row 1. The companion note claims a fresh-batch bound of `A[D+√D log(1/δ)]` using a Freedman-type bounded-deficit argument. I find this plausible, but I did not find it published or verify it; if it holds, it removes the regime gain in row 1. The genuinely new mechanism is the delayed conditioning on the remote momentum tracker plus a stopping/bootstrap argument. This targets exactly the obstacle that Hübler et al. identify in App. D.3 of 2410.13849. Proof ancestry: Hübler et al.'s cosine concentration and robust validation in the style of Ghadimi–Lan; neither supplies the persistent-momentum bound.

**Search coverage.** I searched on 21 Oct 2026 UTC across arXiv and PMLR for high-probability NSGD‑M, Muon, and LMO momentum. I read theorem statements for 2410.13849 (Thm 4, App. D.3), 2606.14560 (Thm 3.5, conclusion), 2106.14343 (Thm 2), and Sfyraki–Wang [2506.04192v4](https://arxiv.org/abs/2506.04192) (Thms 5–6: clipped, constrained, Frank–Wolfe gap, so not comparable). I also checked that [2602.07425v2](https://arxiv.org/abs/2602.07425) and [2605.06884v1](https://arxiv.org/abs/2605.06884) give expected bounds only. I found no prior high-probability result for unclipped persistent NSGD‑M or Muon. The theorem was added on 21 Oct 2026 (commit 31eb907). The companion note's own comparison table is consistent with what I read, except for the unverified fresh-batch claim.

**Conclusion**

**No problem-class speedup is established; what is new is a high-probability guarantee for unmodified persistent-momentum Muon.**

The strongest applicable baseline is minibatch spectral-normalized SGD (no momentum), analyzed via Hübler et al.'s Thm 4 and followed by the same validation. Under the same assumptions and output criterion:

| | Oracle calls (`A=1+s²/ε²`, `R=1+LΔ/ε²`, `ℓ=log(1/δ)`) |
|---|---|
| Batch NSGD + validation | `A·(Rℓ + ℓ²)` up to `log log` |
| This theorem | `A·(R + √R·log²(AR/δ))` |

This theorem wins by at most a factor `ℓ`, and only when `√R·ℓ ≳ log²(AR/δ)`. It loses at fixed `δ` with small `R`, and when `ℓ ≫ R`. A Freedman-type refinement of the baseline, which the companion note itself sketches but which I did not verify, would likely remove even this gain.

The real contribution is method-specific. For persistent EMA normalized momentum with one sample per step (Muon, and Euclidean NSGD‑M when `m=1`), a finite-variance, logarithmic-confidence bound without clipping was explicitly listed as open in 2410.13849 (App. D.3) and in 2606.14560. I found no prior resolution. However, the result covers only `p=2` and needs the stronger row-profile noise assumption, and its validated output still uses batches. So the significance is real but narrow: the answer to an open question for a popular method, not a better optimization guarantee.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
