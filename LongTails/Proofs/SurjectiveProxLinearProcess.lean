import LongTails.Proofs.SurjectiveProxLinearTrajectory
import LongTails.Proofs.SurjectiveProxLinearMoreau
import LongTails.Proofs.SurjectiveProxLinearStability
import LongTails.Proofs.ProxLinearOracleMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearProcess

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearMoreau
open LongTails.Proofs.SurjectiveProxLinearStability
open LongTails.Proofs.SurjectiveProxLinearTuning

noncomputable def estimatorError (p : Params) (I : Problem p)
    (Z : p.E → p.Ω → JointSpace p) (ξ : ℕ → p.Ω) (k : ℕ) : JointSpace p :=
  (trajectory p Z ξ k).2 - jointMean p I (trajectory p Z ξ k).1

noncomputable def estimatedStep (p : Params) (Z : p.E → p.Ω → JointSpace p)
    (ξ : ℕ → p.Ω) (k : ℕ) : p.E :=
  modelStep p ((jointEquiv p).symm (trajectory p Z ξ k).2)

lemma error_norm_identity (p : Params) (I : Problem p) (x : p.E) (z : JointSpace p) :
    ‖z - jointMean p I x‖ ^ 2 =
      ‖((jointEquiv p).symm z).1 - gradient I.f x‖ ^ 2 +
      ‖((jointEquiv p).symm z).2.1 - I.c x‖ ^ 2 +
      ‖((jointEquiv p).symm z).2.2 - I.J x‖ ^ 2 := by
  have h := jointEquiv_sub_norm_sq p ((jointEquiv p).symm z)
    (gradient I.f x, I.c x, I.J x)
  simpa only [ContinuousLinearEquiv.apply_symm_apply, jointMean] using h

lemma trajectory_step_error (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (Z : p.E → p.Ω → JointSpace p) (ξ : ℕ → p.Ω) (k : ℕ) :
    ‖estimatedStep p Z ξ k - exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ≤
      sensitivity p * (‖estimatorError p I Z ξ k‖ ^ 2 + ridge p ^ 2) := by
  rw [norm_sub_rev]
  unfold estimatedStep estimatorError
  rw [error_norm_identity]
  exact model_step_error_squared p I hp H _ _

lemma trajectory_envelope_descent (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (Z : p.E → p.Ω → JointSpace p) (ξ : ℕ → p.Ω) (k : ℕ) :
    envelope p I (trajectory p Z ξ (k + 1)).1 ≤ envelope p I (trajectory p Z ξ k).1 -
      gamma p * relaxation p * ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 +
      6 * gamma p * relaxation p * sensitivity p *
        (‖estimatorError p I Z ξ k‖ ^ 2 + ridge p ^ 2) := by
  have ht := (variance_scales_positive p hp).2.2.2.2.2.le
  have hg := (valid_tuning_positive p hp).2.1.le
  have hd := envelope_perturbed_descent p I hp H (trajectory p Z ξ k).1
    (estimatedStep p Z ξ k) ht (relaxation_le_tenth p hp)
  have he := mul_le_mul_of_nonneg_left (trajectory_step_error p I hp H Z ξ k)
    (show 0 ≤ 6 * gamma p * relaxation p by positivity)
  change envelope p I ((trajectory p Z ξ k).1 + relaxation p • estimatedStep p Z ξ k) ≤ _
  nlinarith

lemma estimated_step_square (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (Z : p.E → p.Ω → JointSpace p) (ξ : ℕ → p.Ω) (k : ℕ) :
    ‖estimatedStep p Z ξ k‖ ^ 2 ≤
      2 * ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 +
      2 * sensitivity p * (‖estimatorError p I Z ξ k‖ ^ 2 + ridge p ^ 2) := by
  have hn := ProxLinearEnvelope.norm_add_sq_two
    (exactModelStep p I (trajectory p Z ξ k).1)
    (estimatedStep p Z ξ k - exactModelStep p I (trajectory p Z ξ k).1)
  have hadd : exactModelStep p I (trajectory p Z ξ k).1 +
      (estimatedStep p Z ξ k - exactModelStep p I (trajectory p Z ξ k).1) =
      estimatedStep p Z ξ k := by abel
  rw [hadd] at hn
  have he := trajectory_step_error p I hp H Z ξ k
  nlinarith

end LongTails.Proofs.SurjectiveProxLinearProcess
