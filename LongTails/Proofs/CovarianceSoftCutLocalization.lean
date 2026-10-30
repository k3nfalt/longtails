import LongTails.Proofs.CovarianceSoftCutTrajectory
import LongTails.Proofs.GdConvex
import LongTails.Proofs.CovarianceSoftCutPotential
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutLocalization

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutDensity

lemma mass_lower_target (q : Params) (α η : ℝ) (cuts : List (Cut q))
    (A : Set (Space q)) (hA : MeasurableSet A)
    (hsub : A ⊆ Metric.closedBall (0 : Space q) (2 * q.R))
    (hA0 : volume A ≠ 0) (hAfinite : volume A ≠ ⊤) :
    (volume A).toReal * Real.exp (-(η * (volume A).toReal⁻¹ * ∫ y in A, lossSum q α cuts y)) ≤
      mass q α η cuts := by
  have hl : IntegrableOn (lossSum q α cuts) A :=
    ((continuous_lossSum q α cuts).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space q) (2 * q.R))).mono_set hsub
  have hc : IntegrableOn (coreWeight q α η cuts) A :=
    ((continuous_coreWeight q α η cuts).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space q) (2 * q.R))).mono_set hsub
  have hj := convexOn_exp.map_set_average_le
    (f := fun y => -η * lossSum q α cuts y) (t := A) (μ := volume)
    Real.continuous_exp.continuousOn isClosed_univ hA0 hAfinite
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) (hl.const_mul (-η)) hc
  simp only [setAverage_eq, Measure.real, smul_eq_mul, integral_const_mul] at hj
  have hm : 0 < (volume A).toReal := ENNReal.toReal_pos hA0 hAfinite
  have hscaled := mul_le_mul_of_nonneg_left hj hm.le
  rw [mul_inv_cancel_left₀ hm.ne'] at hscaled
  have heq : (∫ y in A, coreWeight q α η cuts y) = ∫ y in A, weight q α η cuts y := by
    apply setIntegral_congr_fun hA
    intro y hy
    have hn : ‖y‖ ≤ 2 * q.R := by simpa using hsub hy
    simp [weight, hn]
  have hmass : (∫ y in A, coreWeight q α η cuts y) ≤ mass q α η cuts := by
    rw [heq]
    exact setIntegral_le_integral (integrable_weight q α η cuts)
      (Filter.Eventually.of_forall (weight_nonneg q α η cuts))
  apply le_trans ?_ hmass
  convert hscaled using 1 <;> congr 2
  ring

lemma target_signal_bound (q : Params) (hL : 0 < q.L) (α : ℝ)
    (f : Space q → ℝ) (v : Space q → Space q)
    (hg : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (hlip : ∀ x y, |f x - f y| ≤ q.L * ‖x - y‖)
    (x xstar y : Space q) (hbad : α ≤ f x - f xstar)
    (hy : ‖y - xstar‖ ≤ α / (4 * q.L)) :
    ⟪v x, y - x⟫ ≤ -(3 * α / 4) := by
  have hs := hg x y
  have hl := (le_abs_self (f y - f xstar)).trans (hlip y xstar)
  have hr : q.L * ‖y - xstar‖ ≤ α / 4 := by
    calc
      q.L * ‖y - xstar‖ ≤ q.L * (α / (4 * q.L)) := mul_le_mul_of_nonneg_left hy hL.le
      _ = α / 4 := by field_simp
  linarith

lemma target_ball_subset (q : Params) (hL : 0 < q.L) (hR : 0 < q.R)
    (α : ℝ) (hα : α ≤ q.L * q.R) (xstar : Space q) (hx : ‖xstar‖ ≤ q.R) :
    Metric.closedBall xstar (α / (4 * q.L)) ⊆ Metric.closedBall (0 : Space q) (2 * q.R) := by
  intro y hy
  have hy' : ‖y - xstar‖ ≤ α / (4 * q.L) := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hr : α / (4 * q.L) ≤ q.R / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * q.L)).2
    nlinarith
  have hn := norm_add_le (y - xstar) xstar
  rw [sub_add_cancel] at hn
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

lemma target_volume_ratio (q : Params) (hL : 0 < q.L) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (xstar : Space q) :
    volume.real (Metric.closedBall xstar (α / (4 * q.L))) =
      (α / (8 * q.L * q.R)) ^ q.d * volume.real (Metric.closedBall (0 : Space q) (2 * q.R)) := by
  rw [Measure.addHaar_real_closedBall' volume xstar (by positivity),
    Measure.addHaar_real_closedBall' volume (0 : Space q) (r := 2 * q.R) (by positivity)]
  simp only [Space, finrank_euclideanSpace_fin]
  rw [← mul_assoc, ← mul_pow]
  congr 2
  field_simp
  ring

lemma mass_empty (q : Params) (α η : ℝ) :
    mass q α η [] = volume.real (Metric.closedBall (0 : Space q) (2 * q.R)) := by
  have hw : weight q α η [] = (Metric.closedBall (0 : Space q) (2 * q.R)).indicator (fun _ => (1 : ℝ)) := by
    ext y
    simp [weight, coreWeight, lossSum, Set.indicator, Metric.mem_closedBall, dist_zero_right]
  rw [mass, hw, integral_indicator Metric.isClosed_closedBall.measurableSet]
  simp [Measure.real]

def targetMeasure (q : Params) (α : ℝ) (xstar : Space q) : Measure (Space q) :=
  (volume (Metric.closedBall xstar (α / (4 * q.L))))⁻¹ •
    volume.restrict (Metric.closedBall xstar (α / (4 * q.L)))

lemma targetMeasure_probability (q : Params) (hL : 0 < q.L)
    (α : ℝ) (hα : 0 < α) (xstar : Space q) :
    IsProbabilityMeasure (targetMeasure q α xstar) := by
  have hpos : 0 < volume (Metric.closedBall xstar (α / (4 * q.L))) :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume xstar (by positivity))
      (measure_mono Metric.ball_subset_closedBall)
  have hfinite : volume (Metric.closedBall xstar (α / (4 * q.L))) ≠ ⊤ :=
    (isCompact_closedBall xstar (α / (4 * q.L))).measure_lt_top.ne
  constructor
  simp only [targetMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite

lemma targetMeasure_support (q : Params) (α : ℝ) (xstar : Space q) :
    ∀ᵐ y ∂targetMeasure q α xstar, ‖y-xstar‖ ≤ α / (4 * q.L) := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hy

lemma integral_targetMeasure (q : Params) (α : ℝ) (xstar : Space q) (F : Space q → ℝ) :
    (∫ y, F y ∂targetMeasure q α xstar) =
      (volume (Metric.closedBall xstar (α / (4 * q.L)))).toReal⁻¹ *
        ∫ y in Metric.closedBall xstar (α / (4 * q.L)), F y := by
  rw [targetMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

lemma integrable_targetMeasure_of_continuous (q : Params) (hL : 0 < q.L)
    (α : ℝ) (hα : 0 < α) (xstar : Space q) (F : Space q → ℝ) (hF : Continuous F) :
    Integrable F (targetMeasure q α xstar) := by
  have hpos : 0 < volume (Metric.closedBall xstar (α / (4 * q.L))) :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume xstar (by positivity))
      (measure_mono Metric.ball_subset_closedBall)
  exact (hF.continuousOn.integrableOn_compact (isCompact_closedBall xstar (α / (4 * q.L)))).smul_measure
    (ENNReal.inv_ne_top.mpr hpos.ne')

lemma targetMeasure_lossSum_append (q : Params) (hL : 0 < q.L)
    (α : ℝ) (hα : 0 < α) (xstar : Space q) (cuts : List (Cut q)) (cut : Cut q) :
    (∫ y, lossSum q α (cuts ++ [cut]) y ∂targetMeasure q α xstar) =
      (∫ y, lossSum q α cuts y ∂targetMeasure q α xstar) +
        ∫ y, hinge q α cut y ∂targetMeasure q α xstar := by
  simp_rw [lossSum_append]
  apply integral_add
  · exact integrable_targetMeasure_of_continuous q hL α hα xstar _ (continuous_lossSum q α cuts)
  · exact integrable_targetMeasure_of_continuous q hL α hα xstar _ (continuous_hinge q α cut)

lemma target_log_volume_ratio (q : Params) (hL : 0 < q.L) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (xstar : Space q) :
    Real.log (volume.real (Metric.closedBall (0 : Space q) (2 * q.R))) -
      Real.log (volume.real (Metric.closedBall xstar (α / (4 * q.L)))) =
        (q.d : ℝ) * Real.log (8 * q.L * q.R / α) := by
  have hB : 0 < volume.real (Metric.closedBall (0 : Space q) (2 * q.R)) := by
    rw [← mass_empty q α 0]
    exact mass_pos q hR α 0 []
  have hr : 0 < α / (8 * q.L * q.R) := by positivity
  rw [target_volume_ratio q hL hR α hα xstar,
    Real.log_mul (pow_ne_zero _ hr.ne') hB.ne', Real.log_pow,
    Real.log_div hα.ne' (by positivity), Real.log_div (by positivity) hα.ne']
  ring

lemma generator_targetLoss_lower (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (hαR : α ≤ q.L * q.R)
    (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R) (b T : ℕ) (replies : ℕ → Space q) :
    (T : ℝ) / 6 - (q.d : ℝ) * Real.log (8 * q.L * q.R / α) ≤
      (2 / α) * ∫ y, lossSum q α (List.ofFn (generatorCuts q α (2 / α) b T replies)) y
        ∂targetMeasure q α xstar := by
  let A := Metric.closedBall xstar (α / (4 * q.L))
  have hApos : 0 < volume A := lt_of_lt_of_le
    (Metric.measure_ball_pos volume xstar (by positivity)) (measure_mono Metric.ball_subset_closedBall)
  have hAfin : volume A ≠ ⊤ := (isCompact_closedBall xstar (α / (4 * q.L))).measure_lt_top.ne
  have hreal : 0 < (volume A).toReal := ENNReal.toReal_pos hApos.ne' hAfin
  have hinit : 0 < volume.real (Metric.closedBall (0 : Space q) (2 * q.R)) := by
    rw [← mass_empty q α (2 / α)]
    exact mass_pos q hR α (2 / α) []
  have hlo := mass_lower_target q α (2 / α)
    (List.ofFn (generatorCuts q α (2 / α) b T replies)) A measurableSet_closedBall
    (target_ball_subset q hL hR α hαR xstar hxstar) hApos.ne' hAfin
  have hup := CovarianceSoftCutTrajectory.generator_mass_exp_bound q hd hR α hα b T replies
  rw [mass_empty, mul_comm] at hup
  have hl := CovarianceSoftCutPotential.loss_lower_of_mass_bounds _ _ _ _ (T : ℝ)
    hreal hinit hlo hup
  have he : Real.log (volume.real (Metric.closedBall (0 : Space q) (2 * q.R))) -
      Real.log (volume A).toReal = (q.d : ℝ) * Real.log (8 * q.L * q.R / α) :=
    target_log_volume_ratio q hL hR α hα xstar
  rw [he] at hl
  simpa only [integral_targetMeasure, mul_assoc] using hl

end LongTails.Proofs.CovarianceSoftCutLocalization
