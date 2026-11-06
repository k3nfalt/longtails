import LongTails.Proofs.SurjectiveProxLinearProcess

open MeasureTheory

namespace LongTails.Proofs.SurjectiveProxLinearIntegrability

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearProcess
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearTuning

lemma trajectory_function_integrable (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (hZ : Measurable (Function.uncurry Z))
    (P : Measure (ℕ → p.Ω)) [IsProbabilityMeasure P] (k : ℕ)
    (F : p.E → ℝ) (hF : Continuous F) :
    Integrable (fun ξ => F (trajectory p Z ξ k).1) P := by
  let R := (k : ℝ) * relaxation p * (eta p * (p.H + (rho p * p.m) * p.H))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p.x0 R).image hF).isBounded.exists_norm_le
  have hx := (measurable_trajectory p hp Z hZ k).fst
  apply Integrable.of_bound (hF.measurable.comp hx).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro ξ
  apply hC
  apply Set.mem_image_of_mem
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact trajectory_displacement p hp Z ξ (variance_scales_positive p hp).2.2.2.2.2.le k

lemma measurable_estimatedStep (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (hZ : Measurable (Function.uncurry Z)) (k : ℕ) :
    Measurable (fun ξ => estimatedStep p Z ξ k) := by
  exact (continuous_modelStep p hp).measurable.comp
    ((jointEquiv p).symm.continuous.measurable.comp (measurable_trajectory p hp Z hZ k).snd)

lemma estimated_step_square_integrable (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (hZ : Measurable (Function.uncurry Z))
    (P : Measure (ℕ → p.Ω)) [IsProbabilityMeasure P] (k : ℕ) :
    Integrable (fun ξ => ‖estimatedStep p Z ξ k‖ ^ 2) P := by
  apply Integrable.of_bound ((measurable_estimatedStep p hp Z hZ k).norm.pow_const 2).aestronglyMeasurable
    ((eta p * (p.H + (rho p * p.m) * p.H)) ^ 2)
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := norm_modelStep_le p hp ((jointEquiv p).symm (trajectory p Z ξ k).2)
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h)).mpr h

end LongTails.Proofs.SurjectiveProxLinearIntegrability
