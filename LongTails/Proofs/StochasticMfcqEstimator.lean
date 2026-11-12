import LongTails.Proofs.StochasticMfcqPath
import LongTails.Proofs.RobustPilot

namespace LongTails.Proofs.StochasticMfcqEstimator

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection

lemma joint_norm_sq (p : Params) (v : Primitive p) :
    ‖jointEquiv p v‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖v.1‖ ^ 2 + (‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2) = _
  ring

lemma component_bounds (p : Params) (v : Primitive p) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ‖jointEquiv p v‖ ≤ δ) :
    ‖v.1‖ ≤ δ ∧ (∀ i, |v.2.1 i| ≤ δ) ∧ ∀ i, ‖v.2.2 i‖ ≤ δ := by
  have hs := joint_norm_sq p v
  have hsq := (sq_le_sq₀ (norm_nonneg _) hδ).2 h
  have hg : ‖v.1‖ ≤ δ := by nlinarith [sq_nonneg ‖v.2.1‖, sq_nonneg ‖v.2.2‖]
  have hc : ‖v.2.1‖ ≤ δ := by nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2.2‖]
  have hJ : ‖v.2.2‖ ≤ δ := by nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2.1‖]
  refine ⟨hg, fun i => ?_, fun i => (PiLp.norm_apply_le v.2.2 i).trans hJ⟩
  simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le v.2.1 i).trans hc

lemma estimateAccurate_of_joint_error (p : Params) (I : Problem p) (hp : spec.valid p)
    (x : p.E) (v : Primitive p)
    (h : ‖jointEquiv p v - jointEquiv p (gradient I.f x, I.c x, I.J x)‖ ≤ precision p) :
    StochasticMfcqPath.estimateAccurate p I x v := by
  rw [← map_sub] at h
  exact component_bounds p _ _ (StochasticMfcqTuning.precision_bounds p hp).1.le h

lemma majority_accurate (p : Params) (I : Problem p) (hp : spec.valid p) (x : p.E)
    (estimates : Fin (replicas p) → JointSpace p)
    (h : replicas p < 2 * (Finset.univ.filter (fun i =>
      ‖estimates i - jointEquiv p (gradient I.f x, I.c x, I.J x)‖ ≤
        (2 * precision p) / 6)).card) :
    StochasticMfcqPath.estimateAccurate p I x (robustEstimate p estimates) := by
  apply estimateAccurate_of_joint_error p I hp x
  have hb := OracleTemplate.RobustGradient.pilotCenter_accuracy estimates
    (jointEquiv p (gradient I.f x, I.c x, I.J x)) h
  simpa [robustEstimate] using hb

end LongTails.Proofs.StochasticMfcqEstimator
