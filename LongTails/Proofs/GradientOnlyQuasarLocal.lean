import LongTails.Proofs.RelativeGeneralizedLocal

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GradientOnlyQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma local_gradient_descent {f : E → ℝ} {g : E → E} {L0 L1 D : ℝ} {u x : E}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hD : 0 ≤ D)
    (hf : ∀ w, HasGradientAt f (g w) w) (hg : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (hm : IsMinOn f univ u) (hgap : f x - f u ≤ D) :
    f (x - (1 / (128 * (L0 + L1 ^ 2 * D))) • g x) ≤
      f x - ‖g x‖ ^ 2 / (256 * (L0 + L1 ^ 2 * D)) := by
  let C := L0 + L1 ^ 2 * D
  let η := 1 / (128 * C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η * C = 1 / 128 := by dsimp [η]; field_simp
  have hG := RelativeGeneralized.scalar_gradient_gap (norm_nonneg (g x)) hL0.le hL1 hD
    (RelativeGeneralized.gap_gradient_square hL0 hL1 hf hg hs hm hgap)
  have hG' : ‖g x‖ ≤ 9 * Real.sqrt (L0 * D) + 32 * L1 * D := by
    nlinarith [Real.sqrt_nonneg (L0 * D), mul_nonneg hL1 hD]
  have hcurv := RelativeGeneralized.query_curvature_bound hL0.le hL1 hD hG'
  have hsmall : η * (L0 + L1 * ‖g x‖) ≤ 49 / 128 := by
    have hh := mul_le_mul_of_nonneg_left hcurv hη.le
    change η * (L0 + L1 * ‖g x‖) ≤ η * (49 * C) at hh
    nlinarith [hηC]
  have hr : L1 * (η * ‖g x‖) ≤ 1 / 2 := by
    nlinarith [mul_nonneg hη.le hL0.le]
  let w := x - η • g x
  have hw : w - x = -(η • g x) := by dsimp [w]; abel
  have hdist : ‖w - x‖ = η * ‖g x‖ := by
    rw [hw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hup := CompositeGeneralized.ball_upper hL0.le hL1 hf hg hs hr
    (x := x) (u := x) (v := w) (by simp; positivity) hdist.le
  rw [hw, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hup
  have hb : (L0 + L1 * ‖g x‖) * (η * ‖g x‖) ^ 2 ≤ η / 2 * ‖g x‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ η * ‖g x‖ ^ 2 by positivity)
    nlinarith [mul_nonneg hη.le (sq_nonneg ‖g x‖)]
  have hout : f w ≤ f x - η / 2 * ‖g x‖ ^ 2 := by linarith
  have heq : η / 2 * ‖g x‖ ^ 2 = ‖g x‖ ^ 2 / (256 * C) := by dsimp [η]; ring
  rw [heq] at hout
  exact hout

end OracleTemplate.GradientOnlyQuasar
