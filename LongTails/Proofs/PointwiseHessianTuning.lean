import LongTails.Algorithms.PointwiseHessianAccelerated
import LongTails.Proofs.PointwiseHessianNewton
import LongTails.Proofs.CompositeCubicAcceleration

namespace LongTails.Proofs.PointwiseHessianTuning

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated

lemma continuationRatio_pos (p : Public) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 ≤ r) : 0 < continuationRatio p τ r := by
  unfold continuationRatio
  positivity

lemma continuationRatio_identity (p : Public) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 ≤ r) :
    continuationRatio p τ r * (1 + p.M₁ * r ^ 2 + (1 / τ) * p.M₀ * r) = 1 / 64 := by
  have hd : 0 < 1 + p.M₁ * r ^ 2 + p.M₀ * r / τ := by positivity
  have he : (1 / τ) * p.M₀ * r = p.M₀ * r / τ := by ring
  rw [he]
  unfold continuationRatio
  field_simp

lemma radiusCap_pos (p : Public) (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R)
    {τ : ℝ} (hτ : 0 < τ) : 0 < radiusCap p τ := by
  unfold radiusCap
  split_ifs with h
  · positivity
  · have hp : 0 < p.M₀ := lt_of_le_of_ne hM₀ (Ne.symm h)
    positivity

lemma initialRadius_pos (p : Public) (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R)
    (hε : 0 < p.ε) {τ : ℝ} (hτ : 0 < τ) : 0 < initialRadius p τ := by
  have hc := radiusCap_pos p hM₀ hR hτ
  unfold initialRadius gradientThreshold
  positivity

lemma initialRegularization_pos (p : Public) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (g : p.E) (hg : g ≠ 0) :
    0 < initialRegularization p τ r g := by
  have ha := continuationRatio_pos p hM₀ hM₁ hτ hr.le
  have hn := norm_pos_iff.mpr hg
  unfold initialRegularization
  positivity

lemma initialRegularization_residual (p : Public) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (g : p.E) (hg : g ≠ 0) :
    ‖initialRegularization p τ r g • g‖ ≤ continuationRatio p τ r * r / 4 := by
  have hb := initialRegularization_pos p hM₀ hM₁ hτ hr g hg
  have hn := norm_pos_iff.mpr hg
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
  have hh := mul_le_mul_of_nonneg_right
    (min_le_right (1 / τ) (continuationRatio p τ r * r / (4 * ‖g‖))) hn.le
  unfold initialRegularization
  apply hh.trans_eq
  field_simp

lemma initialWeight_pos (p : Public) (hR : 0 < p.R) (hΔ : 0 < p.Δ) :
    0 < initialWeight p := by unfold initialWeight; positivity

lemma weight_pos {A η : ℝ} (hA : 0 ≤ A) (hη : 0 < η) : 0 < weight A η :=
  CompositeCubicAcceleration.trialWeight_pos hη hA

lemma weight_identity {A η : ℝ} (hA : 0 ≤ A) (hη : 0 < η) :
    η * weight A η ^ 2 = A + weight A η :=
  CompositeCubicAcceleration.trialWeight_identity hη hA

lemma continuationRatio_le (p : Public) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 ≤ r) : continuationRatio p τ r ≤ 1 / 64 := by
  have ha := (continuationRatio_pos p hM₀ hM₁ hτ hr).le
  have hi := continuationRatio_identity p hM₀ hM₁ hτ hr
  have hx : 0 ≤ p.M₁ * r ^ 2 := by positivity
  have hy : 0 ≤ (1 / τ) * p.M₀ * r := by positivity
  nlinarith [mul_nonneg ha (add_nonneg hx hy)]

lemma radiusCap_le (p : Public) (τ : ℝ) : radiusCap p τ ≤ 16 * p.R := by
  unfold radiusCap
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma radiusCap_scaled (p : Public) (hM₀ : 0 ≤ p.M₀) {τ r : ℝ}
    (hτ : 0 < τ) (hr : r ≤ radiusCap p τ) : p.M₀ * r / τ ≤ 1 / 64 := by
  by_cases h : p.M₀ = 0
  · simp [h]
  · have hp : 0 < p.M₀ := lt_of_le_of_ne hM₀ (Ne.symm h)
    have hc : radiusCap p τ ≤ τ / (64 * p.M₀) := by
      simp only [radiusCap, h, ite_false]
      exact min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 64 * p.M₀ by positivity)).mp (hr.trans hc)
    apply (div_le_iff₀ hτ).mpr
    nlinarith

end LongTails.Proofs.PointwiseHessianTuning
