import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace LongTails.Proofs.CenteredLogisticExpansion

lemma sigmoid_deviation (x : ℝ) : |Real.sigmoid x - 1 / 2| ≤ |x| / 4 := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (Real.hasDerivAt_sigmoid t).hasDerivWithinAt)
    (C := (1 / 4 : ℝ)) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sigmoid_nonneg _)
        (sub_nonneg.mpr (Real.sigmoid_le_one _)))]
      nlinarith [sq_nonneg (Real.sigmoid t - 1 / 2)])
    (Set.mem_univ 0) (Set.mem_univ x)
  simp only [Real.sigmoid_zero, Real.norm_eq_abs, sub_zero] at h
  convert h using 1 <;> ring_nf

lemma sigmoid_cubic (x : ℝ) : |Real.sigmoid x - 1 / 2 - x / 4| ≤ |x| ^ 3 / 16 := by
  let s := Set.Icc (-|x|) |x|
  have h := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ s) => (((Real.hasDerivAt_sigmoid t).sub_const (1 / 2)).sub
      ((hasDerivAt_id t).div_const 4)).hasDerivWithinAt)
    (C := |x| ^ 2 / 16) (fun t ht => by
      simp only [Real.norm_eq_abs]
      rw [show Real.sigmoid t * (1 - Real.sigmoid t) - 1 / 4 =
        -(Real.sigmoid t - 1 / 2) ^ 2 by ring, abs_neg, abs_of_nonneg (sq_nonneg _)]
      have hd := (sigmoid_deviation t).trans
        (div_le_div_of_nonneg_right (abs_le.mpr ht) (by norm_num))
      nlinarith [sq_abs (Real.sigmoid t - 1 / 2),
        mul_self_le_mul_self (abs_nonneg _) hd])
    (show 0 ∈ s from ⟨by linarith [abs_nonneg x], abs_nonneg x⟩)
    (show x ∈ s from ⟨neg_abs_le x, le_abs_self x⟩)
  change ‖(Real.sigmoid x - 1 / 2 - x / 4) - (Real.sigmoid 0 - 1 / 2 - 0 / 4)‖ ≤ _ at h
  norm_num [Real.norm_eq_abs] at h
  rw [← sq_abs x] at h
  convert h using 1
  ring

end LongTails.Proofs.CenteredLogisticExpansion
