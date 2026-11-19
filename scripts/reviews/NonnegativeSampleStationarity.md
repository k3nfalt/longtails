# Novelty review: expected stationarity for nonnegative smooth sample losses (upper bound)

[`result`](../../LongTails/Theorems/NonnegativeSampleStationarity.lean) shows the following for `F(x) = E_ξ ℓ_ξ(x)` on a separable Hilbert space, where every sample loss is nonnegative with an `L`-Lipschitz gradient, the sample gradient is jointly measurable, samples are IID, and `F(x₀) ≤ Δ` ([setup](../../LongTails/Setups/NonnegativeSmoothSampleLoss.lean)). Normalized STORM with an initial minibatch and a uniformly random output index ([algorithm](../../LongTails/Algorithms/NormalizedStorm.lean)) returns `X` with `E‖∇F(X)‖ ≤ ε` within `⌈8192(1 + LΔ/ε²)^{3/2}⌉` same-sample pair calls.

**Complexity.** Each pair call returns two gradients of one fresh sample:

  `O(1 + (LΔ)^{3/2}/ε³)`

Here `L` is the per-sample smoothness constant, `Δ ≥ F(x₀)` bounds the initial risk itself rather than the gap `F(x₀) − inf F`, and `ε` is the target `E‖∇F‖`. The `LΔ/ε²` term is absorbed, because `(1+R)^{3/2} ≍ 1 + R^{3/2}`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository: [NormalizedStormExpectedSmoothness](../../LongTails/Theorems/NormalizedStormExpectedSmoothness.lean) (added 2026-10-16, before this result), normalized STORM under MSS + ABC variance. *Covers the full target setup* through the reduction below, with `A = L`, `C = 0`, `lower = 0`. | `O(1 + LΔ/ε² + (LΔ)^{3/2}/ε³)` → `O(1 + (LΔ)^{3/2}/ε³)` | None: same order (same algorithm and tuning, `tS/tA/tEta/tB0/tT` at `A = L, C = 0`) | None. The new class is a subclass of ABC + MSS; the theorem only restates the hypotheses at the sample level. | None (same random-iterate output, same known `L, Δ, ε`) | None beyond the narrower class |
| [Khaled–Richtárik, TMLR 2023](https://arxiv.org/abs/2002.03329), Prop. 2 + Cor. 1: SGD under expected smoothness. *Covers the full setup.* Prop. 2 gives `A = L`, `B = 0`, `C = 2L·inf F ≤ 2LΔ`. | `O(1 + L²Δ²/ε⁴)` (min-iterate `E‖∇F‖² ≤ ε²`, which converts by Jensen to a random iterate) → `O(1 + (LΔ)^{3/2}/ε³)` | Factor `≍ √(LΔ)/ε` when `ε² ≤ LΔ`. When `ε² ≥ 2LΔ`, both are `O(1)`. | None | None | Needs the same-sample pair oracle (2 gradients per call). SGD needs one gradient per call and uses `L_F ≤ L`. |
| [Chen–Zhou–Liang–Lu, ICML 2023](https://arxiv.org/abs/2303.02854), Thm 4: SPIDER under affine variance `Γ²‖∇F‖² + Λ²`. *Applies only to instances that also satisfy affine variance.* | Repository retuning (constants unchecked): `O((LΔ(1+Γ²)+Λ²)/ε² + LΔ(1+Γ)Λ/ε³)` → `O(1 + (LΔ)^{3/2}/ε³)` | Mixed on the overlap. This result is better if `(1+Γ)Λ ≫ √(LΔ)`. It is worse when `Λ ≪ √(LΔ)/(1+Γ)`; for example, `Λ = 0` gives `ε⁻²` for them and `ε⁻³` here. | Affine variance → nonnegative smooth samples. The classes are incomparable (example below). | None | Uses the pair oracle instead of minibatches |

**Scope check.** Take `ℓ_± = F ± φ` with Rademacher signs. Set `F = c√(1+x²)` and `φ′ = s cos s` with `s = (1+x²)^{1/4}`. Then `|φ″| ≤ 1`, `|φ| = O(1+|x|)`, and for large `c`, `ℓ_± ≥ 0` with bounded `F″`. The variance `φ′²` is unbounded while `|F′| ≤ c`, so affine variance fails. This one-dimensional example is artificial. It shows only that the class is not contained in the affine-variance class; it is not a natural application.

**Reduction and ancestry.** The result follows by standard reduction. The self-bound `‖∇ℓ_ξ‖² ≤ 2Lℓ_ξ` ([Srebro–Sridharan–Tewari 2010](https://arxiv.org/abs/1009.3896), Lemma 2.1, with the looser constant `4L`; Khaled–Richtárik Prop. 2) gives ABC with `A = L, C = 0, lower = 0`. Per-sample smoothness gives MSS, and the [moment-transfer module](../../LongTails/Proofs/NonnegativeSampleMoments.lean) derives unbiasedness and integrability. The repository's ABC theorem is then applied verbatim ([proof](../../LongTails/Proofs/NonnegativeSampleStorm.lean)). The only new work is measure-theoretic bookkeeping. The ABC theorem itself rests on the normalized-STORM analysis of [Cutkosky–Mehta 2020](https://arxiv.org/abs/2002.03305).

**Search coverage.** On 2026-11-18 I searched arXiv, the proceedings and the web for STORM/SPIDER under expected smoothness, ABC, self-bounded, nonnegative-loss and Blum–Gladyshev noise. I found no earlier published `ε⁻³` theorem for this class. I relied on the earlier repository review for the details of Chen et al. Thm 4 and [Upadhyay et al. 2605.15314](https://arxiv.org/abs/2605.15314), whose `ε⁻⁴` bound is weaker here, and did not re-read those papers. The result was introduced on 2026-11-18 (commit `6af6a91`). The companion note itself says the upper rate "is a specialization" of the existing theorem and places the contribution in the [lower bound](../../LongTails/Theorems/NonnegativeSampleStationarityLowerBound.lean), which is not assessed here. I found no discrepancy with the note.

**Conclusion**

**No: this is a direct corollary of a result already in the repository, with no new rate or scope.**

The strongest baseline is the repository's normalized-STORM theorem under expected-smoothness (ABC) noise, added a month earlier. For nonnegative `L`-smooth sample losses, ABC holds with `A = L`, `C = 0` by the textbook self-bound `‖∇ℓ‖² ≤ 2Lℓ`. Substituting these values gives exactly this theorem's algorithm, tuning and order:

| Method | Pair-call / gradient budget |
|---|---|
| SGD (Khaled–Richtárik) | `1 + L²Δ²/ε⁴` |
| Repository ABC STORM, `A = L, C = 0` | `1 + (LΔ)^{3/2}/ε³` |
| **This result** | `1 + (LΔ)^{3/2}/ε³` |

Against SGD, the `√(LΔ)/ε` gain is real for `ε² ≤ LΔ`. That gain belongs to the earlier ABC theorem, and the new setup is a subclass of it. On instances that also satisfy affine variance, Chen et al.'s SPIDER bound can be better, by up to a factor `1/ε` when the noise floor `Λ` is small.

My search found no published `ε⁻³` guarantee for this class, but the novelty question concerns the repository's own earlier result, not missing literature. What this theorem contributes is a formal sample-level restatement of an existing guarantee, a useful companion to the lower bound but not a new result on its own.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
