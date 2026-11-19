import LongTails.Proofs.WeightedSphericalMoments
import Mathlib.Analysis.Normed.Module.Normalize

open MeasureTheory Set Metric NormedSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SphericalPreferenceAlignment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_alignment (g u : E) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖g‖ ^ 2 - ⟪g, u⟫ ^ 2 ≤
      2 * (‖g‖ + r) * ⟪g, normalize (g + r • u) - u⟫ := by
  let w := g + r • u
  let t := ‖w‖
  let a := ⟪w, u⟫
  let b := ⟪g, normalize w - u⟫
  have ht : 0 ≤ t := norm_nonneg _
  have ha : a ≤ t := by simpa [a, t, hu] using real_inner_le_norm w u
  have htR : t ≤ ‖g‖ + r := by
    simpa [t, w, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu] using norm_add_le g (r • u)
  have hau : a = ⟪g, u⟫ + r := by
    simp [a, w, inner_add_left, real_inner_smul_left, hu]
  have hts : t ^ 2 = ‖g‖ ^ 2 + 2 * r * ⟪g, u⟫ + r ^ 2 := by
    simp [t, w, norm_add_sq_real, real_inner_smul_right, norm_smul, hu, abs_of_nonneg hr,
      Real.norm_eq_abs]
    ring
  have htb : t * b = (t + r) * (t - a) := by
    have hgw : t * ⟪g, normalize w⟫ = ⟪g, w⟫ := by
      rw [← real_inner_smul_right, norm_smul_normalize]
    have hinner : ⟪g, w⟫ = ‖g‖ ^ 2 + r * ⟪g, u⟫ := by
      simp [w, inner_add_right, real_inner_smul_right]
    dsimp only [b]
    rw [inner_sub_right, mul_sub, hgw, hinner]
    rw [hau]
    nlinarith only [hts]
  have hb : 0 ≤ b := by
    rcases ht.eq_or_lt with h | h
    · have hw : w = 0 := norm_eq_zero.mp h.symm
      have hg : g = -(r • u) := eq_neg_of_add_eq_zero_left hw
      simp [b, hw, hg, real_inner_smul_left, hu, hr]
    · exact nonneg_of_mul_nonneg_right (htb.ge.trans' (mul_nonneg (by linarith) (sub_nonneg.mpr ha))) h
  change _ ≤ 2 * (‖g‖ + r) * b
  calc
    _ = t ^ 2 - a ^ 2 := by rw [hau]; nlinarith only [hts]
    _ ≤ 2 * t * b := by nlinarith only [htb, sq_nonneg (t - a), mul_nonneg hr (sub_nonneg.mpr ha)]
    _ ≤ _ := by nlinarith only [mul_nonneg (sub_nonneg.mpr htR) hb]

end LongTails.Proofs.SphericalPreferenceAlignment
