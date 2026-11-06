import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SubGaussianMatrixNet

lemma norm_of_inner_net {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (V : Set E) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ y, ‖y‖ = 1 → ∃ v ∈ V, ‖y - v‖ ≤ 1 / 8)
    (hbound : ∀ v ∈ V, |⟪x, v⟫| ≤ B) : ‖x‖ ≤ 2 * B := by
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
  have hxy : ⟪x, y⟫ = ‖x‖ := by
    simp only [y, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  obtain ⟨v, hv, hyv⟩ := hV y hy
  have hvbound := (le_abs_self ⟪x, v⟫).trans (hbound v hv)
  have hrem := (real_inner_le_norm x (y - v)).trans
    (mul_le_mul_of_nonneg_left hyv (norm_nonneg x))
  rw [inner_sub_right, hxy] at hrem
  linarith

lemma operator_norm_of_bilinear_net {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E →L[ℝ] F) (U : Set E) (V : Set F) (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ x, ‖x‖ = 1 → ∃ u ∈ U, ‖x - u‖ ≤ 1 / 8)
    (hV : ∀ y, ‖y‖ = 1 → ∃ v ∈ V, ‖y - v‖ ≤ 1 / 8)
    (hUnorm : ∀ u ∈ U, ‖u‖ ≤ 2)
    (hbound : ∀ u ∈ U, ∀ v ∈ V, |⟪L u, v⟫| ≤ B) : ‖L‖ ≤ 2 * B := by
  have hL : 0 ≤ ‖L‖ := norm_nonneg _
  have hunit (x : E) (hx : ‖x‖ = 1) : ‖L x‖ ≤ B + 3 * ‖L‖ / 8 := by
    by_cases hzero : L x = 0
    · rw [hzero, norm_zero]
      positivity
    have hn : 0 < ‖L x‖ := norm_pos_iff.mpr hzero
    let y := ‖L x‖⁻¹ • L x
    have hy : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
    have hxy : ⟪L x, y⟫ = ‖L x‖ := by
      simp only [y, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    obtain ⟨u, hu, hxu⟩ := hU x hx
    obtain ⟨v, hv, hyv⟩ := hV y hy
    have hfirst := (le_abs_self ⟪L u, v⟫).trans (hbound u hu v hv)
    have hsecond : ⟪L (x - u), y⟫ ≤ ‖L‖ / 8 := by
      have h := (real_inner_le_norm (L (x - u)) y).trans
        (mul_le_mul_of_nonneg_right (L.le_opNorm (x - u)) (norm_nonneg y))
      rw [hy, mul_one] at h
      have hsmall := mul_le_mul_of_nonneg_left hxu hL
      linarith
    have hthird : ⟪L u, y - v⟫ ≤ ‖L‖ / 4 := by
      have h := (real_inner_le_norm (L u) (y - v)).trans
        (mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg (y - v)))
      have hsmall := mul_le_mul_of_nonneg_left hyv (mul_nonneg hL (norm_nonneg u))
      have hun := mul_le_mul_of_nonneg_left (hUnorm u hu) hL
      nlinarith
    have heq : ⟪L x, y⟫ = ⟪L u, v⟫ + ⟪L (x - u), y⟫ + ⟪L u, y - v⟫ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [hxy] at heq
    linarith
  have h := ContinuousLinearMap.opNorm_le_of_unit_norm
    (f := L) (show 0 ≤ B + 3 * ‖L‖ / 8 by positivity) hunit
  linarith

end LongTails.Proofs.SubGaussianMatrixNet
