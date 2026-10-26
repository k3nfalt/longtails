import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.RelativeCurvatureSpectrum

namespace LongTails.Proofs.RelativeCurvatureValidation

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rayleigh_difference (C : E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M) (hC : ‖C‖ ≤ M)
    (u v : E) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |⟪u, C u⟫ - ⟪v, C v⟫| ≤ 2 * M * ‖u - v‖ := by
  have he : ⟪u, C u⟫ - ⟪v, C v⟫ = ⟪u - v, C u⟫ + ⟪v, C (u - v)⟫ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h₁ := abs_real_inner_le_norm (u - v) (C u)
  have h₂ := abs_real_inner_le_norm v (C (u - v))
  have hc₁ : ‖C u‖ ≤ M := ((C.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))).trans (by nlinarith)
  have hc₂ := (C.le_opNorm (u - v)).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  have hm₁ := mul_le_mul_of_nonneg_left hc₁ (norm_nonneg (u - v))
  have hm₂ := mul_le_mul_of_nonneg_left hc₂ (norm_nonneg v)
  have hm₃ := mul_le_mul_of_nonneg_right hv (mul_nonneg hM (norm_nonneg (u - v)))
  rw [he]
  have h := abs_add_le ⟪u - v, C u⟫ ⟪v, C (u - v)⟫
  nlinarith

lemma normalized_rayleigh_stability (C : E →L[ℝ] E) (hC : ‖C‖ ≤ 2)
    {a : ℝ} (_ha : 0 ≤ a) (ha₁ : a ≤ 1) (w z : E)
    (hw : 4 ≤ ‖w‖) (he : ‖z - w‖ ≤ a / 128) :
    z ≠ 0 ∧ |⟪‖z‖⁻¹ • z, C (‖z‖⁻¹ • z)⟫ -
      ⟪‖w‖⁻¹ • w, C (‖w‖⁻¹ • w)⟫| ≤ a / 64 := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖w‖)
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    simp only [zero_sub, norm_neg] at he
    linarith
  have hd := CubicRegularization.normalized_distance w z hw0 hz0
  rw [norm_sub_rev w z] at hd
  have hdist : ‖‖w‖⁻¹ • w - ‖z‖⁻¹ • z‖ ≤ a / 256 := by
    have hp := mul_le_mul_of_nonneg_right hw (norm_nonneg (‖w‖⁻¹ • w - ‖z‖⁻¹ • z))
    nlinarith
  have hn (v : E) (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
    simp [norm_smul, norm_ne_zero_iff.mpr hv]
  have hr := rayleigh_difference C (by norm_num : (0 : ℝ) ≤ 2) hC
    (‖z‖⁻¹ • z) (‖w‖⁻¹ • w) (hn z hz0).le (hn w hw0).le
  rw [norm_sub_rev (‖z‖⁻¹ • z) (‖w‖⁻¹ • w)] at hr
  exact ⟨hz0, hr.trans (by linarith)⟩

lemma approximate_rayleigh_error (C : E →L[ℝ] E) (v q : E) {e : ℝ}
    (hv : ‖v‖ ≤ 1) (he : ‖q - C v‖ ≤ e) :
    |⟪v, q⟫ - ⟪v, C v⟫| ≤ e := by
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm v (q - C v)).trans
    ((mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans (by simpa using he))

lemma normalized_negative_rayleigh (C : E →L[ℝ] E) {a : ℝ} (_ha : 0 < a)
    (w : E) (hw : 16 ≤ a * ‖w‖ ^ 2)
    (hq : ⟪w, C w⟫ + a * ‖w‖ ^ 2 ≤ 2) :
    ⟪‖w‖⁻¹ • w, C (‖w‖⁻¹ • w)⟫ ≤ -7 * a / 8 := by
  have hn : 0 < ‖w‖ := by
    by_contra h
    have hz : ‖w‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz] at hw
    norm_num at hw
  have he : ⟪‖w‖⁻¹ • w, C (‖w‖⁻¹ • w)⟫ = ⟪w, C w⟫ / ‖w‖ ^ 2 := by
    simp only [map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith

lemma validation_complete (C : E →L[ℝ] E) (hC : ‖C‖ ≤ 2)
    {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (w z q : E)
    (hw : 16 ≤ a * ‖w‖ ^ 2) (hq : ⟪w, C w⟫ + a * ‖w‖ ^ 2 ≤ 2)
    (he : ‖z - w‖ ≤ a / 128)
    (hp : ‖q - C (‖z‖⁻¹ • z)‖ ≤ a / 16) :
    z ≠ 0 ∧ ⟪‖z‖⁻¹ • z, q⟫ ≤ -a / 2 := by
  have hw₁ : 4 ≤ ‖w‖ := by
    have h := mul_le_mul_of_nonneg_right ha₁ (sq_nonneg ‖w‖)
    nlinarith [norm_nonneg w]
  obtain ⟨hz, hr⟩ := normalized_rayleigh_stability C hC ha.le ha₁ w z hw₁ he
  have hn : ‖‖z‖⁻¹ • z‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hz]
  have hv := normalized_negative_rayleigh C ha w hw hq
  have hp' := approximate_rayleigh_error C (‖z‖⁻¹ • z) q hn.le hp
  obtain ⟨_, hr⟩ := abs_le.mp hr
  obtain ⟨_, hp'⟩ := abs_le.mp hp'
  exact ⟨hz, by linarith⟩

lemma validation_sound (C : E →L[ℝ] E) {a : ℝ} (v q : E)
    (hv : ‖v‖ ≤ 1) (hp : ‖q - C v‖ ≤ a / 16)
    (ht : ⟪v, q⟫ ≤ -a / 2) : ⟪v, C v⟫ ≤ -7 * a / 16 := by
  have he := (abs_le.mp (approximate_rayleigh_error C v q hv hp)).1
  linarith

end LongTails.Proofs.RelativeCurvatureValidation
