# MuonMomentumSeparation: novelty assessment

The [theorem](../../LongTails/Theorems/MuonMomentumSeparation.lean) is stated on the [setup](../../LongTails/Setups/MomentumSpectralSmooth.lean) and runs `muonMomentum` ([algorithm](../../LongTails/Algorithms/MomentumDirection.lean)): exact-polar Muon with EMA momentum at a public, fixed β ∈ [0,1), batch B, step η = (1−β)ε/(8L), and a uniformly random iterate X_τ. It proves 𝔼‖∇f(X_τ)‖_* ≤ ε on every admissible instance. Inside `successful` it also proves two lower bounds. For every η > 0, B ≥ 1 and T, SGD-M (dir = id) and Frobenius-normalized NSGD-M at the *same* β fail on some admissible instance unless N = B(T+1) satisfies

  N ≥ min{ ½√(n−r+1), (r−1)(1−β)³LΔs²/(2²¹ε⁴) },  with r = min(m,n) ≥ 2 and LΔ ≥ 1024ε².

**Complexity.** The proved budget is (⌈128(1−β)s²/ε²⌉+1)(⌈(32LΔ/ε²+16)/(1−β)⌉+1), which gives

  N = O( 1 + s²/ε² + LΔs²/ε⁴ + (1 + LΔ/ε²)/(1−β) ).

The parameters mean the following:
- L: smoothness, ‖∇f(X)−∇f(Y)‖_* ≤ L‖X−Y‖_op.
- Δ: the initial gap f(X₀) − inf f.
- s: the row-profile noise bound, Σσᵢ ≤ s with 𝔼‖(G−∇f)ᵀbᵢ‖² ≤ σᵢ², under IID unbiased sampling.
- ε: the target nuclear-norm accuracy.
- β: the shared momentum parameter.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tao–Yu–Zhang, [arXiv 2605.06615](https://arxiv.org/abs/2605.06615) v1 (7 May 2026), Thm 4: batched Muon without momentum. It assumes one-sided noise; under the row profile its proof gives the same bound ([review](MuonNoiseSeparation.md)). The repository's [MuonNoiseSeparation](../../LongTails/Theorems/MuonNoiseSeparation.lean) does the same. | O(1 + s²/ε² + LΔ/ε² + LΔs²/ε⁴) → O(1 + s²/ε² + LΔs²/ε⁴ + (1+LΔ/ε²)/(1−β)) | Worse by a factor 1/(1−β) on the deterministic term; same order at β = 0. | None | None: both return a uniform iterate under expected nuclear stationarity. | The momentum buffer gives no complexity benefit here, and the batch still scales like (1−β)s²/ε². |
| Repository [MuonNoiseSeparation](../../LongTails/Theorems/MuonNoiseSeparation.lean) with `SeparationLower.nsgd_lower_bound` / `sgd_lower_bound` (2026-10-23): competitor lower bounds at β = 0. | NSGD: N ≥ (r−1)LΔs²/(2.1·10⁷ε⁴(2+log(1+s√r/ε))). SGD: N ≥ (r−1)LΔs²/(1728ε⁴) → N ≥ min{½√(n−r+1), (r−1)(1−β)³LΔs²/(2²¹ε⁴)} | Not an upper-bound gain. At β = 0 the NSGD log factor disappears, but only when n − r + 1 > 4N². | Competitors without momentum → competitors with fixed EMA momentum β. | None | Adds a width condition n ≳ m + 4N² and a factor (1−β)³. The bound is vacuous for tall matrices and as β → 1. |
| Kidambi et al. ([ICLR 2018](https://arxiv.org/abs/1803.05591)); Kim–Yun ([NeurIPS 2026 OPT workshop](https://neurips.cc/virtual/2026/161480), full text not read): fixed-β heavy-ball momentum, including SHB, Signum and Muon, does not beat the method without momentum. Applicability: different geometry and criteria; neither covers NSGD-M. | Not comparable | Not comparable | None | None | The SGD-M half is an instance of this known phenomenon, as the note concedes. |

**Regime check.** In the noise-dominated regime, Muon-M's budget is about 2¹²LΔs²/ε⁴. The competitor lower bound exceeds it only if (r−1)(1−β)³ > 2³³ ≈ 8.6·10⁹ and n ≳ (2¹³LΔs²/ε⁴)².

The lower bound does not cover NSGD-M as Cutkosky–Mehta ([ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html)) actually run it, with 1−β ≍ ε²/σ² and B = 1. In that regime the bound degrades by (ε/s)⁶. On the witness, Muon coincides with blockwise-normalized momentum SGD.

**Standard-reduction check and proof ancestry.** The upper bound is the batched-Muon descent argument of TYZ and the repository, extended with a standard EMA lag/noise bound. The repository's [FiniteVarianceMuonHighProbability](../../LongTails/Theorems/FiniteVarianceMuonHighProbability.lean) already treats momentum Muon in this class with high probability.

The NSGD-M lower bound does not follow from the β = 0 lemma. Its new mechanism has three parts:
- a birthday-bound event on which the one-hot noise is fresh and orthogonal at every step;
- an exact impulse-response reduction for the EMA;
- a band argument that controls the correlated normalizer ‖M_t‖_F.

Hübler–Pethick–Sra ([arXiv 2606.14560](https://arxiv.org/abs/2606.14560) v1, Thms 3.7–3.8) give class lower bounds for all first-order methods under their moment noise model, not algorithm-specific NSGD-M bounds. I did not verify that their model coincides with the row profile.

**Search coverage.** I searched arXiv, the web and the NeurIPS listings on 2026-10-31. I read the theorem lists of TYZ v1 (no momentum or NSGD lower bounds) and HPS v1 (no NSGD-M or SGD-specific lower bounds). For Kim–Yun I saw only the listing abstract; it names SHB, Signum and Muon, not NSGD-M.

The theorem was introduced on 2026-10-30 (commit 56a0aae). The companion note's claims match the Lean statement, and it candidly disclaims the upper bound and the SGD-M half. I did not run the build or the comparator.

**Conclusion**

**No complexity or scope improvement; the only new piece is a fixed-β lower bound for Frobenius-normalized SGD with momentum.**

On the optimization side, the strongest baseline is batched Muon without momentum (Tao–Yu–Zhang Thm 4, and the repository's MuonNoiseSeparation):

| | Calls for 𝔼‖∇f(X̂)‖_* ≤ ε |
|---|---|
| Muon, β = 0 | O(1 + s²/ε² + LΔ/ε² + LΔs²/ε⁴) |
| This Muon-M | O(1 + s²/ε² + LΔs²/ε⁴ + (1+LΔ/ε²)/(1−β)) |

Momentum therefore never helps and costs a factor 1/(1−β) when the deterministic term dominates.

The lower bound N ≥ min{½√(n−r+1), (r−1)(1−β)³LΔs²/(2²¹ε⁴)} extends the repository's earlier momentum-free NSGD/SGD bounds to a shared fixed β. It is weak in three concrete ways:
- It is vacuous in the β → 1 regime where NSGD-M is tuned in theory.
- It needs n ≳ N², and r(1−β)³ > 8.6·10⁹ before it beats Muon's budget.
- The SGD-M half restates the known fact that fixed-β momentum does not help SGD.

I found no prior NSGD-M lower bound in nuclear geometry, but the search was targeted and Kim–Yun was unread, so priority is supported but not established.

What can be claimed is a formally verified, asymptotic-in-r separation between Muon-M and fixed-β NSGD-M/SGD-M on extremely wide matrices, with no new upper-bound guarantee.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
