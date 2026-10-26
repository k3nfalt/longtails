import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic
import LongTails.Proofs.HessianLipschitzModel

namespace LongTails.Proofs.ReusedCurvatureCertificate

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma absolute_lower_of_relative {H B : E →L[ℝ] E} {a δ : ℝ}
    (ha : 0 ≤ a)
    (hrelative : ∀ v, -a * ⟪v, B v⟫ ≤ ⟪v, H v⟫)
    (herror : ∀ v, ⟪v, B v⟫ - δ * ‖v‖ ^ 2 ≤ ⟪v, H v⟫) :
    ∀ v, -(a * δ / (1 + a)) * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  intro v
  have hp : 0 < 1 + a := by positivity
  have he := mul_le_mul_of_nonneg_left (herror v) ha
  have hr := hrelative v
  have hi : -(a * δ / (1 + a)) * ‖v‖ ^ 2 =
      -(a * δ * ‖v‖ ^ 2) / (1 + a) := by ring
  rw [hi]
  apply (div_le_iff₀ hp).mpr
  nlinarith

lemma absolute_lower_of_relative_simple {H B : E →L[ℝ] E} {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hrelative : ∀ v, -a * ⟪v, B v⟫ ≤ ⟪v, H v⟫)
    (herror : ∀ v, ⟪v, B v⟫ - δ * ‖v‖ ^ 2 ≤ ⟪v, H v⟫) :
    ∀ v, -(a * δ) * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  intro v
  have he := mul_le_mul_of_nonneg_left (herror v) ha
  have hr := hrelative v
  by_cases hh : 0 ≤ ⟪v, H v⟫
  · exact (neg_nonpos.mpr (mul_nonneg ha hδ) |> fun h =>
      mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)).trans hh
  · have hh' : a * ⟪v, H v⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hh)
    nlinarith

lemma negative_direction_of_relative {H B : E →L[ℝ] E} {a δ : ℝ} {v : E}
    (ha : 0 ≤ a) (hB : δ * ‖v‖ ^ 2 ≤ ⟪v, B v⟫)
    (hrelative : ⟪v, H v⟫ ≤ -a * ⟪v, B v⟫) :
    ⟪v, H v⟫ ≤ -(a * δ) * ‖v‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hB ha
  nlinarith

lemma relative_witness_of_absolute {H B : E →L[ℝ] E} {a δ γ : ℝ} {v : E}
    (ha : 0 ≤ a) (hγ : a * δ ≤ γ)
    (herror : ⟪v, B v⟫ ≤ ⟪v, H v⟫ + δ * ‖v‖ ^ 2)
    (hnegative : ⟪v, H v⟫ < -γ * ‖v‖ ^ 2)
    (hγ0 : 0 ≤ γ) :
    ⟪v, H v⟫ < -a * ⟪v, B v⟫ := by
  have hn : ⟪v, H v⟫ < 0 := hnegative.trans_le
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ0) (sq_nonneg _))
  have he := mul_le_mul_of_nonneg_left herror ha
  have hg := mul_le_mul_of_nonneg_right hγ (sq_nonneg ‖v‖)
  have hha := mul_nonpos_of_nonneg_of_nonpos ha hn.le
  nlinarith

lemma finite_difference_error {g : E → E} {M h : ℝ}
    (hM : 0 ≤ M) (hh : 0 < h) (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M * ‖x - y‖)
    (x v : E) :
    ‖h⁻¹ • (g (x + h • v) - g x) - fderiv ℝ g x v‖ ≤ M * h * ‖v‖ ^ 2 := by
  have he := OracleTemplate.NonlinearTemporalDiscrepancy.gradient_linearization_bound
    hM hg hH x (x + h • v)
  simp only [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hh] at he
  have hi : h⁻¹ • (g (x + h • v) - g x) - fderiv ℝ g x v =
      h⁻¹ • (g (x + h • v) - g x - h • fderiv ℝ g x v) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [hi, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  calc
    _ ≤ h⁻¹ * (M * (h * ‖v‖) ^ 2) := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hh.le)
    _ = _ := by field_simp

lemma preconditioned_finite_difference_error {g : E → E} {M h : ℝ}
    (hM : 0 ≤ M) (hh : 0 < h) (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M * ‖x - y‖)
    (D : E →L[ℝ] E) (x z : E) :
    ‖D (h⁻¹ • (g (x + h • D z) - g x)) - D (fderiv ℝ g x (D z))‖ ≤
      M * h * ‖D‖ ^ 3 * ‖z‖ ^ 2 := by
  rw [← map_sub]
  calc
    _ ≤ ‖D‖ * ‖h⁻¹ • (g (x + h • D z) - g x) - fderiv ℝ g x (D z)‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (M * h * ‖D z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_difference_error hM hh hg hH x (D z)) (norm_nonneg _)
    _ ≤ ‖D‖ * (M * h * (‖D‖ * ‖z‖) ^ 2) := by
      gcongr
      exact D.le_opNorm z
    _ = _ := by ring

lemma adjoint_finite_difference_error [CompleteSpace E] {g : E → E} {M h : ℝ}
    (hM : 0 ≤ M) (hh : 0 < h) (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M * ‖x - y‖)
    (D : E →L[ℝ] E) (x z : E) :
    ‖D.adjoint (h⁻¹ • (g (x + h • D z) - g x)) - D.adjoint (fderiv ℝ g x (D z))‖ ≤
      M * h * ‖D‖ ^ 3 * ‖z‖ ^ 2 := by
  rw [← map_sub]
  calc
    _ ≤ ‖D‖ * ‖h⁻¹ • (g (x + h • D z) - g x) - fderiv ℝ g x (D z)‖ := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using D.adjoint.le_opNorm _
    _ ≤ ‖D‖ * (M * h * ‖D z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_difference_error hM hh hg hH x (D z)) (norm_nonneg _)
    _ ≤ ‖D‖ * (M * h * (‖D‖ * ‖z‖) ^ 2) := by
      gcongr
      exact D.le_opNorm z
    _ = _ := by ring

end LongTails.Proofs.ReusedCurvatureCertificate
