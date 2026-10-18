import LongTails.Algorithms.QuarticMetricStage
import LongTails.Proofs.GuardedMetricDescent

namespace LongTails.Proofs.QuarticStageTrial

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def coefficient (p : Parameters E) (y : Point E) : ℝ :=
  min p.L⁻¹ (p.r / (2 * ‖transformedGradient p.S (gradient p y)‖))

lemma coefficient_nonneg (p : Parameters E) (y : Point E) (hL : 0 < p.L) (hr : 0 ≤ p.r) :
    0 ≤ coefficient p y := by unfold coefficient; positivity

lemma coefficient_upper (p : Parameters E) (y : Point E) (hL : 0 < p.L) :
    p.L * coefficient p y ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_left (min_le_left p.L⁻¹
    (p.r / (2 * ‖transformedGradient p.S (gradient p y)‖))) hL.le
  simpa only [coefficient, mul_inv_cancel₀ hL.ne'] using hh

lemma trial_displacement (p : Parameters E) (y : Point E) :
    p.S (trialPoint p y - y.x) = -(coefficient p y • transformedGradient p.S (gradient p y)) := by
  simp [trialPoint, coefficient]

lemma trial_radius (p : Parameters E) (y : Point E) (hL : 0 < p.L) (hr : 0 ≤ p.r) :
    ‖p.S (trialPoint p y - y.x)‖ ≤ p.r / 2 := by
  rw [trial_displacement, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (coefficient_nonneg p y hL hr)]
  by_cases hz : ‖transformedGradient p.S (gradient p y)‖ = 0
  · rw [hz, mul_zero]
    positivity
  have hh := mul_le_mul_of_nonneg_right
    (min_le_right p.L⁻¹ (p.r / (2 * ‖transformedGradient p.S (gradient p y)‖)))
    (norm_nonneg (transformedGradient p.S (gradient p y)))
  have he : p.r / (2 * ‖transformedGradient p.S (gradient p y)‖) *
      ‖transformedGradient p.S (gradient p y)‖ = p.r / 2 := by field_simp
  exact hh.trans_eq he

lemma trial_descent (p : Parameters E) (y next : Point E) (hL : 0 < p.L) (hr : 0 ≤ p.r)
    (hnext : next.x = trialPoint p y)
    (hmodel : value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
      p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2) :
    value p next ≤ value p y - coefficient p y / 2 * ‖transformedGradient p.S (gradient p y)‖ ^ 2 := by
  have hmove : p.S (next.x - y.x) = -(coefficient p y • transformedGradient p.S (gradient p y)) := by
    rw [hnext]
    exact trial_displacement p y
  rw [GuardedMetricDescent.metric_pairing p.S, hmove, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hmodel
  have hh := mul_le_mul_of_nonneg_right (coefficient_upper p y hL)
    (mul_nonneg (coefficient_nonneg p y hL hr) (sq_nonneg ‖transformedGradient p.S (gradient p y)‖))
  nlinarith

lemma trial_full (p : Parameters E) (y next : Point E) {A : ℝ}
    (hL : 0 < p.L) (hr : 0 < p.r) (hα : 0 ≤ p.α) (hA : A ≤ p.r / 8)
    (hq : p.q ≤ p.L * p.r ^ 2 / 16)
    (hnext : next.x = trialPoint p y)
    (hsupport : value p y ≤ p.center.value + ‖transformedGradient p.S (gradient p y)‖ * A)
    (hdescent : value p next ≤ value p y - coefficient p y / 2 * ‖transformedGradient p.S (gradient p y)‖ ^ 2)
    (hnoprogress : p.center.value - p.q < next.value) :
    p.S next.x = gradientStep p.L (p.S y.x) (transformedGradient p.S (gradient p y)) := by
  have hvalue : next.value ≤ value p next := by
    unfold value regularizedValue
    exact le_add_of_nonneg_right (by positivity)
  have hh := GuardedMetricDescent.no_progress_full_coefficient hL hr
    (norm_nonneg (transformedGradient p.S (gradient p y))) hA hq hsupport hdescent
    (hnoprogress.trans_le hvalue)
  rcases hh with hz | ht
  · have hg := norm_eq_zero.mp hz
    simp [hnext, trialPoint, gradientStep, hg]
  · change coefficient p y = p.L⁻¹ at ht
    have he : p.S next.x - p.S y.x = -(coefficient p y • transformedGradient p.S (gradient p y)) := by
      rw [← map_sub, hnext, trial_displacement]
    rw [ht] at he
    unfold gradientStep
    calc
      _ = (p.S next.x - p.S y.x) + p.S y.x := by abel
      _ = _ := by rw [he]; abel

lemma full_step_descent (p : Parameters E) (y next : Point E) (hL : 0 < p.L)
    (hfull : p.S next.x = gradientStep p.L (p.S y.x) (transformedGradient p.S (gradient p y)))
    (hmodel : value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
      p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2) :
    value p next ≤ value p y - ‖transformedGradient p.S (gradient p y)‖ ^ 2 / (2 * p.L) := by
  have hm : p.S (next.x - y.x) = -(p.L⁻¹ • transformedGradient p.S (gradient p y)) := by
    rw [map_sub, hfull, gradientStep]
    abel
  rw [GuardedMetricDescent.metric_pairing p.S, hm, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hmodel
  have he : value p y - p.L⁻¹ * ‖transformedGradient p.S (gradient p y)‖ ^ 2 +
      p.L / 2 * (p.L⁻¹ ^ 2 * ‖transformedGradient p.S (gradient p y)‖ ^ 2) =
      value p y - ‖transformedGradient p.S (gradient p y)‖ ^ 2 / (2 * p.L) := by
    field_simp
    ring
  simpa only [← sub_eq_add_neg, he] using hmodel

end LongTails.Proofs.QuarticStageTrial
