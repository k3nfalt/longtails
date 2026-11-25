import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LogisticCloudDispersion

lemma sigmoid_secant (a b : ℝ) :
    ∃ s ∈ Set.Icc (0 : ℝ) (1 / 4), Real.sigmoid a - Real.sigmoid b = s * (a - b) := by
  have bound {x y : ℝ} (h : x < y) :
      ∃ s ∈ Set.Icc (0 : ℝ) (1 / 4), Real.sigmoid y - Real.sigmoid x = s * (y - x) := by
    have hdiff := image_sub_le_mul_sub_of_deriv_le
      (fun z => (Real.hasDerivAt_sigmoid z).differentiableAt)
      (C := (1 / 4 : ℝ)) (fun z => by
        rw [Real.deriv_sigmoid]
        nlinarith [sq_nonneg (Real.sigmoid z - 1 / 2)]) h.le
    refine ⟨_, ⟨div_nonneg (sub_nonneg.mpr (Real.sigmoid_monotone h.le)) (sub_nonneg.mpr h.le),
      (div_le_iff₀ (sub_pos.mpr h)).mpr hdiff⟩, ?_⟩
    field_simp [(sub_pos.mpr h).ne']
  rcases lt_trichotomy a b with h | rfl | h
  · obtain ⟨s, hs, he⟩ := bound h
    exact ⟨s, hs, by linarith⟩
  · exact ⟨0, ⟨le_rfl, by norm_num⟩, by simp⟩
  · exact bound h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rank_one_step (x u : E) {k : ℝ} (hk : 0 ≤ k) (ht : k * ‖u‖ ^ 2 ≤ 2) :
    ‖x - (k * ⟪u, x⟫) • u‖ ≤ ‖x‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg x)
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm x u, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  nlinarith only [mul_nonneg (mul_nonneg hk (sq_nonneg ⟪x, u⟫))
    (sub_nonneg.mpr ht)]

lemma transverse_step (x u : E) (c : ℝ) {η : ℝ} (hη : 0 ≤ η) (ht : η * ‖u‖ ^ 2 ≤ 8) :
    ‖x - (η * (Real.sigmoid (c + ⟪u, x⟫) - Real.sigmoid c)) • u‖ ≤ ‖x‖ := by
  obtain ⟨s, ⟨hs, hs'⟩, he⟩ := sigmoid_secant (c + ⟪u, x⟫) c
  rw [add_sub_cancel_left] at he
  rw [he, ← mul_assoc]
  apply rank_one_step x u (mul_nonneg hη hs)
  nlinarith [mul_le_mul_of_nonneg_left hs' (mul_nonneg hη (sq_nonneg ‖u‖))]

end LongTails.Proofs.LogisticCloudDispersion
