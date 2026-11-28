# BrightnessLogisticFirstFit: novelty assessment

The [theorem](../../LongTails/Theorems/BrightnessLogisticFirstFit.lean) proves the following for constant-step full-batch GD on the average logistic loss of the bilinear model `c₁⟨X,v⟩ + c₂⟨SX,v⟩`, with both layers trained and the first strictly fitting iterate returned ([setup](../../LongTails/Setups/BrightnessLogisticJoint.lean), [algorithm](../../LongTails/Algorithms/FirstFitGradientDescent.lean)). On rows `Xᵢ = R dᵢ e + zᵢ` it reaches strict fit (`0 <` every score) deterministically within the budget. `allowedAlgorithm` enforces exactly this GD update, the stop-on-flag rule and the output.

**Parameters.** `n` is the number of rows and `R` the brightness scale. `|dᵢ| ≤ D` bounds the brightness coefficients, `J` bounds `‖Aᵢ‖+‖Cᵢ‖`, where `A,C = (I∓S)z/√2`, and `γ` is the unit-separator margin of the `Aᵢ`. `P,Q` are the initial tap sum and difference, `t,w` the initial readout, and `a,g` the initialization-gap certificate. With `L = 1+log 2n`, the proved budget is

```
N = O( n R (1+D) J F M · exp((6L+22J+5J²)(M+1)) ),
F = 1+3(P²+t²)+Q²+‖w‖²,
M = 1 + 2(‖a‖+√(P²+Q²+2t²+3L+4))/(γg) + 4(3L+1)/(γg)².
```

The constants in the exponent are the exact ones. The bound is linear in `R` and quasi-polynomial in `n`, since the exponent contains `≈72 log²(2n)/(γg)²`. It holds only above a large brightness threshold. For example, the `occupation` condition alone forces `R ≥ 2²²(1+D)(1+JB)J³B³(M+1)³/μ²`, where `B = F·exp((6L+22J+5J²)(M+1))`. Besides margin and initialization conditions, the theorem also requires two-sided brightness mass `μ` and the near-orthogonality condition `2B(M+1)²|⟨Cᵢ,Aⱼ⟩| ≤ g²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Standard reduction (same joint oracle, no `family`): freeze the taps at `(1/√2, −1/√2)`, start the readout at 0 and run GD on the readout with step `1/J²`. The rows become `Aᵢ`, and smooth-convex GD gives the bound. | `O(1 + nJ² log²(2n)/γ²)` → `N` above | **Worse**: the baseline is independent of `R`, polynomial in `n`, and needs no `D, μ, g` or initialization terms. | None. The baseline needs only the margin and the `J` bound. | None. Both return a last iterate certified by the fit flag. | The selected method needs an `R` threshold, the cross condition and a tap-gap initialization. The baseline is excluded only by `allowedAlgorithm`. |
| Constant-step raw GD; repository pair [BrightnessLogisticRawLowerBound](../../LongTails/Theorems/BrightnessLogisticRawLowerBound.lean) (`Ω(R²/log R)` for every step) | `≥ ⌊R² mδ/(8H²)·min(1, debt/(2B_raw log R))⌋` → `O(R·C)`, where `C` is the non-`R` factor of `N` | Factor `≈ R/log R` for fixed other parameters, once `R/log R ≫ nC·H²/(mδ·debt)` and `R` exceeds the validity threshold. | Not comparable: different parameterization of the same linear classifier. | None | The raw lower bound has its own conditions (lattice mass, `debt`, `δ`). I did not verify that its parameter set and the joint parameter set overlap. |
| [Zhang–Wu–Lin–Bartlett](https://arxiv.org/abs/2504.04105), Thm 2.1 (Apr 2025; JMLR v27). Applicability: raw rows normalized by `RD+J`, margin `γ/√2`. | `O((RD+J)²/γ²)` → `N` | Better in `R` (`R` vs `R²`) at large `R`, with a huge `C`. | None | Their bound is for the averaged iterate and uses loss-adaptive steps; the selected result is a last iterate with a constant step. | Their method needs the loss value, which this oracle does not return. Applied to centered rows (the `e` direction is known), their bound becomes `O(J²/γ²)`. |

**Reduction check and proof ancestry.** With fixed zero-sum taps, `(I−S)` cancels the brightness exactly (`Se = e`). So, in the same oracle model, the `R`-dependence is removable by a routine reduction, and the `R`-linear bound is purely method-specific. The proof's new ingredients are the occupation estimate for the brightness logit, the discounted layer-imbalance estimate and the first-fit vote-mass argument ([Residence](../../LongTails/Proofs/BrightnessLogisticResidence.lean), [Imbalance](../../LongTails/Proofs/BrightnessLogisticImbalance.lean)). [Tyurin, arXiv 2512.11587](https://arxiv.org/abs/2512.11587) (v1 Dec 2025, v2 May 2026) supplies the model `m_cv` and the joint-vs-linear CIFAR motivation. It proves `Θ̃(√d/μ)` vs `Ω(d/μ)` only for two-sample perceptron dynamics (Thms 5.1–5.2, as summarized from the HTML). That is a different instance class, so it is motivation and proof ancestry, not a competitor. Arora et al. (ICML 2018) and Gunasekar et al. (NeurIPS 2018) give implicit-acceleration and implicit-bias ancestry, without first-fit rates for this model.

**Search coverage.** I searched on 2026-11-28 UTC, covering arXiv, PMLR and JMLR on separable-logistic GD rates (Soudry/Nacson, Ji–Telgarsky, Wu et al. COLT 2024, Zhang et al. 2025, [Wen et al. 2610.01459](https://arxiv.org/abs/2610.01459)) and two-layer and convolutional linear networks. I found no prior finite-time first-fit bound for jointly trained two-tap GD under brightness scaling. Zhang et al.'s lower bound (Thm 3.2) and Tyurin's Section 5 were read only as summaries. The theorem was introduced in commit `09e4fb3d` (2026-11-28), so every cited work predates it. The companion note's claim of a separation "at least order `R/log R`" compares two GD parameterizations. It does not mention that the same oracle admits an `R`-free method; it does concede that a fixed zero-sum filter removes brightness. I ran no build or audit.

## Conclusion

**No optimization advantage is established; what is new is a method-specific analysis of jointly trained two-tap GD.**

On this instance class, the strongest applicable method uses the very same joint-gradient oracle with the taps frozen at a zero-sum filter. That filter cancels the brightness direction exactly, and plain GD on the readout then fits all rows within an `R`-independent number of calls:

| Method | Full-batch calls to strict fit |
|---|---|
| Frozen zero-sum filter + readout GD | `O(1 + nJ² log²(2n)/γ²)` |
| Joint GD (this theorem) | `O(nR(1+D)JFM·exp((6L+22J+5J²)(M+1)))`, valid only for very large `R` |
| Raw GD (repository pair) | `Ω(R²/log R)` |

The theorem beats raw GD by a factor of about `R/log R`, but only once `R` exceeds a threshold that is exponential in `M`, and the overlap of the two theorems' parameter sets is unverified. It never beats the frozen-filter baseline. What can be claimed is a first finite-step proof, as far as this search found, that jointly trained two-tap logistic GD has first-fit time linear rather than quadratic in brightness, under near-orthogonality and initialization conditions. The theorem's `family` restriction confines the claim to that GD method; it does not make the method competitive.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
