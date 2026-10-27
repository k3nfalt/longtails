import LongTails.Proofs.GdConvex
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.CoarseGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma coarse_energy_step {f : E → ℝ} {x y z u w h : E} {A a D P : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hsearch : f y ≤ f x + D / 256)
    (halign : ⟪h, y - z⟫ ≤ D / 256)
    (hsupport : f y - f u + P ≤ ⟪h, y - u⟫)
    (hdescent : f w ≤ f y - D / 32)
    (hweight : a ^ 2 * ‖h‖ ^ 2 = (A + a) * D / 128 + a * P / 2) :
    (A + a) * (f w - f u) + 1 / 2 * ‖z - a • h - u‖ ^ 2 +
      1 / 2 * a ^ 2 * ‖h‖ ^ 2 ≤
        A * (f x - f u) + 1 / 2 * ‖z - u‖ ^ 2 := by
  have hi : ⟪h, z - u⟫ = ⟪h, y - u⟫ - ⟪h, y - z⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hs := mul_le_mul_of_nonneg_left hsearch hA
  have hd := mul_le_mul_of_nonneg_left hdescent (add_nonneg hA ha)
  have hp := mul_le_mul_of_nonneg_left hsupport ha
  have hl := mul_le_mul_of_nonneg_left halign ha
  have hn : z - a • h - u = (z - u) - a • h := by abel
  rw [hn, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm (z - u) h, hi]
  have hsq : 0 ≤ a ^ 2 * ‖h‖ ^ 2 := by positivity
  have hAD : 0 ≤ A * D := mul_nonneg hA hD
  have haD : 0 ≤ a * D := mul_nonneg ha hD
  nlinarith

lemma coarse_step_distance {y u h : E} {η P : ℝ}
    (hη : 0 ≤ η) (hsupport : P ≤ ⟪h, y - u⟫)
    (hstep : η * ‖h‖ ^ 2 ≤ 2 * P) :
    ‖y - η • h - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  have hn : y - η • h - u = (y - u) - η • h := by abel
  rw [hn, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm (y - u) h]
  have hp := mul_le_mul_of_nonneg_left hsupport hη
  have hs := mul_le_mul_of_nonneg_left hstep hη
  nlinarith

lemma quadratic_weight_identity {S D P A : ℝ} (hS : 0 < S) (hD : 0 < D)
    (hP : 0 ≤ P) (hA : 0 ≤ A) :
    let c := D / 128 + P / 2
    let a := (c + Real.sqrt (c ^ 2 + A * D * S / 32)) / (2 * S)
    0 < a ∧ a ^ 2 * S = (A + a) * D / 128 + a * P / 2 := by
  dsimp only
  let c := D / 128 + P / 2
  let r := Real.sqrt (c ^ 2 + A * D * S / 32)
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hd : 0 ≤ c ^ 2 + A * D * S / 32 := by positivity
  have hs : r ^ 2 = c ^ 2 + A * D * S / 32 := Real.sq_sqrt hd
  change 0 < (c + r) / (2 * S) ∧ _
  constructor
  · positivity
  · change ((c + r) / (2 * S)) ^ 2 * S =
      (A + (c + r) / (2 * S)) * D / 128 + (c + r) / (2 * S) * P / 2
    have hcn : c = D / 128 + P / 2 := rfl
    field_simp
    nlinarith [sq_nonneg (c + r)]

end OracleTemplate.CoarseGeneralized
