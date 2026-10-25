import LongTails.Proofs.ReusedCurvatureCorrection
import LongTails.Proofs.MonotoneCurvatureGeometry
import LongTails.Proofs.MonotoneCurvatureTuning

namespace LongTails.Proofs.MonotoneCurvatureModel

open LongTails.Algorithms.GuardedMetricAcceleration
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_model {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    {H δ α : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (c x y : E)
    (hmetric : δ * ‖y - x‖ ^ 2 ≤ ‖S (y - x)‖ ^ 2)
    (hupper : ⟪y - x, A x (y - x)⟫ ≤ ‖S (y - x)‖ ^ 2)
    (hsmall : H * ‖y - x‖ ≤ δ) (hα : α ≤ δ) :
    regularizedValue α c y (f y) ≤ regularizedValue α c x (f x) +
      ⟪regularizedGradient α c x (g x), y - x⟫ + 4 * ‖S (y - x)‖ ^ 2 := by
  have ht := (abs_le.mp (CubicRegularization.objective_taylor hf hg hLip x (y - x))).2
  rw [add_sub_cancel] at ht
  have hd := GuardedMetricDescent.regularization_difference α (f y) (f x) c y x (g x)
  have hr := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖y - x‖)
  have ha := mul_le_mul_of_nonneg_right hα (sq_nonneg ‖y - x‖)
  nlinarith [sq_nonneg ‖S (y - x)‖]

lemma snapshot_difference {A : E → E →L[ℝ] E} {H δ : ℝ}
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (s x : E) (hr : H * ‖x - s‖ ≤ δ) (v : E) :
    |⟪v, A x v⟫ - ⟪v, A s v⟫| ≤ δ * ‖v‖ ^ 2 := by
  rw [← inner_sub_right, ← sub_apply]
  have h := abs_real_inner_le_norm v ((A x - A s) v)
  have hn := ((A x - A s).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((hLip x s).trans hr) (norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  nlinarith

lemma snapshot_order {A : E → E →L[ℝ] E} {H δ : ℝ}
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (s x : E) (hr : H * ‖x - s‖ ≤ δ) (v : E) :
    ⟪v, A s v⟫ - δ * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫ ∧
      ⟪v, A x v⟫ ≤ ⟪v, A s v⟫ + δ * ‖v‖ ^ 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp (snapshot_difference hLip s x hr v)
  constructor <;> linarith

section
variable [FiniteDimensional ℝ E]

lemma trial_model {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    {H δ R b : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (p : LongTails.Algorithms.QuarticMetricStage.Parameters E)
    (hH : 0 ≤ H) (hb : 0 < b) (hL : p.L = 8) (hr : 0 ≤ p.r)
    (hα : p.α ≤ δ)
    (hmetric : ∀ v, δ * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2)
    (hinverse : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2)
    (hupper : ∀ y, ‖p.S (y - p.center.x)‖ ≤ R →
      ∀ v, ⟪v, A y v⟫ ≤ ‖p.S v‖ ^ 2)
    (hsmall : H * (p.r / 2 / b) ≤ δ)
    (x y : LongTails.Algorithms.QuarticMetricStage.Point E)
    (hxf : x.value = f x.x) (hxg : x.gradient = g x.x) (hyf : y.value = f y.x)
    (hx : ‖p.S (x.x - p.center.x)‖ ≤ R)
    (hy : y.x = LongTails.Algorithms.QuarticMetricStage.trialPoint p x) :
    LongTails.Algorithms.QuarticMetricStage.value p y ≤
      LongTails.Algorithms.QuarticMetricStage.value p x +
      ⟪LongTails.Algorithms.QuarticMetricStage.gradient p x, y.x - x.x⟫ +
      p.L / 2 * ‖p.S (y.x - x.x)‖ ^ 2 := by
  have ht := QuarticStageTrial.trial_radius p x (by rw [hL]; norm_num) hr
  rw [← hy] at ht
  have hi := MonotoneCurvatureGeometry.inverse_radius p.S hb hinverse (p.S (y.x - x.x))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hi
  have hd : ‖y.x - x.x‖ ≤ p.r / 2 / b :=
    hi.trans (div_le_div_of_nonneg_right ht hb.le)
  have hs : H * ‖y.x - x.x‖ ≤ δ := (mul_le_mul_of_nonneg_left hd hH).trans hsmall
  have hm := regularized_model hf hg hLip p.S p.center.x x.x y.x
    (hmetric _) (hupper x.x hx _) hs hα
  simpa only [LongTails.Algorithms.QuarticMetricStage.value,
    LongTails.Algorithms.QuarticMetricStage.gradient, hxf, hxg, hyf, hL,
    show (8 : ℝ) / 2 = 4 by norm_num] using hm

lemma tuned_trial_model {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    {H γ t : ℝ} (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (c : LongTails.Algorithms.QuarticMetricStage.Point E)
    (hmetric : ∀ v, (t ^ 2 * γ) * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hupper : ∀ y, ‖S (y - c.x)‖ ≤ MonotoneCurvatureTuning.metricRadius H γ t →
      ∀ v, ⟪v, A y v⟫ ≤ ‖S v‖ ^ 2)
    (x y : LongTails.Algorithms.QuarticMetricStage.Point E)
    (hxf : x.value = f x.x) (hxg : x.gradient = g x.x) (hyf : y.value = f y.x)
    (hx : ‖S (x.x - c.x)‖ ≤ MonotoneCurvatureTuning.metricRadius H γ t)
    (hy : y.x = LongTails.Algorithms.QuarticMetricStage.trialPoint
      (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t) x) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    LongTails.Algorithms.QuarticMetricStage.value p y ≤
      LongTails.Algorithms.QuarticMetricStage.value p x +
      ⟪LongTails.Algorithms.QuarticMetricStage.gradient p x, y.x - x.x⟫ +
      p.L / 2 * ‖S (y.x - x.x)‖ ^ 2 := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  have ht0 : 0 < t := by linarith
  have hb : 0 < t * Real.sqrt γ := by positivity
  have hsq : (t * Real.sqrt γ) ^ 2 = t ^ 2 * γ := by rw [mul_pow, Real.sq_sqrt hγ.le]
  have hα : γ ≤ t ^ 2 * γ := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ t ^ 2 by nlinarith) hγ.le]
  have hr : 0 ≤ p.r := (MonotoneCurvatureTuning.scales S c hH hγ ht).2.2.2.2.1.le
  have he : p.r / 2 / (t * Real.sqrt γ) = 128 * MonotoneCurvatureTuning.distanceScale H γ := by
    have hs := (Real.sqrt_pos.mpr hγ).ne'
    dsimp [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters, MonotoneCurvatureTuning.distanceScale]
    field_simp
    ring
  have hsmall : H * (p.r / 2 / (t * Real.sqrt γ)) ≤ t ^ 2 * γ := by
    rw [he]
    have hh := MonotoneCurvatureTuning.small_query_radius hH hγ ht
    have hd := MonotoneCurvatureTuning.distanceScale_pos hH hγ
    nlinarith
  exact trial_model hf hg hLip p hH.le hb rfl hr hα hmetric
    (fun v => by rw [hsq]; exact hmetric v) hupper hsmall x y hxf hxg hyf hx hy

end

end LongTails.Proofs.MonotoneCurvatureModel
