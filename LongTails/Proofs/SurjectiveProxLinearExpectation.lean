import LongTails.Proofs.SurjectiveProxLinearMoments
import LongTails.Proofs.SurjectiveProxLinearIntegrability

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearExpectation

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearProcess
open LongTails.Proofs.SurjectiveProxLinearMoments
open LongTails.Proofs.SurjectiveProxLinearIntegrability
open LongTails.Proofs.SurjectiveProxLinearTuning

lemma initial_error_moment (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) :
    Integrable (fun ξ => ‖estimatorError p I (jointOracle p g v D) ξ 0‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) ∧
    (∫ ξ, ‖estimatorError p I (jointOracle p g v D) ξ 0‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) ≤ p.σ ^ 2 / initialBatch p := by
  have h := adaptive_batch_variance p I hp H g v D μ O
    (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) (fun k ξ => ξ k)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid (μ : Measure p.Ω))
    0 (initialBatch p) (initialBatch_pos p) (fun _ => p.x0) measurable_const
  simpa only [estimatorError, trajectory, initialEstimator, Nat.zero_add] using h

lemma next_point_displacement_sq (p : Params) (z : p.E × JointSpace p) :
    ‖nextPoint p z - z.1‖ ^ 2 = relaxation p ^ 2 *
      ‖modelStep p ((jointEquiv p).symm z.2)‖ ^ 2 := by
  simp only [nextPoint, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma recursive_error_moment (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (k : ℕ)
    (hE : Integrable (fun ξ => ‖estimatorError p I (jointOracle p g v D) ξ k‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) :
    Integrable (fun ξ => ‖estimatorError p I (jointOracle p g v D) ξ (k + 1)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) ∧
    (∫ ξ, ‖estimatorError p I (jointOracle p g v D) ξ (k + 1)‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) ≤
      (1 - beta p) ^ 2 * (∫ ξ, ‖estimatorError p I (jointOracle p g v D) ξ k‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) +
      2 * beta p ^ 2 * p.σ ^ 2 + 2 * p.H ^ 2 * relaxation p ^ 2 *
        (∫ ξ, ‖estimatedStep p (jointOracle p g v D) ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) := by
  let Z := jointOracle p g v D
  let S := fun ξ : ℕ → p.Ω => trajectory p Z ξ k
  let U : p.E × JointSpace p → JointSpace p := fun z => z.2 - jointMean p I z.1
  let w : p.E × JointSpace p → ℝ := fun z =>
    2 * beta p ^ 2 * p.σ ^ 2 + 2 * p.H ^ 2 * ‖nextPoint p z - z.1‖ ^ 2
  have hZ := jointOracle_measurable p I g v D μ O
  have hS := measurable_trajectory p hp Z hZ k
  have hM := (jointMean_continuous p I H (le_trans (by norm_num) hp.2.1)).measurable
  have hU : Measurable U := measurable_snd.sub (hM.comp measurable_fst)
  have hstep := estimated_step_square_integrable p hp Z hZ
    (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) k
  have hw (ξ : ℕ → p.Ω) : w (S ξ) = 2 * beta p ^ 2 * p.σ ^ 2 +
      (2 * p.H ^ 2 * relaxation p ^ 2) * ‖estimatedStep p Z ξ k‖ ^ 2 := by
    dsimp only [w, S]
    rw [next_point_displacement_sq]
    unfold estimatedStep
    ring
  have hwi : Integrable (fun ξ => w (S ξ))
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) := by
    simp_rw [hw]
    exact (integrable_const _).add (hstep.const_mul _)
  have hfresh := OracleTemplate.NormalizedStorm.fresh_step_sq (μ : Measure p.Ω)
    (initialBatch p + k) S hS (fun ξ ξ' h => trajectory_congr p Z k h) U hU
    (innovation p I Z) (innovation_measurable p I hp H Z hZ)
    (fun z => (innovation_moments p I hp g v D μ O z).1)
    (fun z => (innovation_moments p I hp g v D μ O z).2.1)
    (fun z => (innovation_moments p I hp g v D μ O z).2.2.1)
    w (fun z => (innovation_moments p I hp g v D μ O z).2.2.2) hwi hE (1 - beta p)
  have hrec (ξ : ℕ → p.Ω) : estimatorError p I Z ξ (k + 1) =
      (1 - beta p) • U (S ξ) + innovation p I Z (S ξ) (ξ (initialBatch p + k)) :=
    error_recursion p I Z ξ k
  dsimp only [Z] at hrec
  have hbound := hfresh.2
  simp_rw [hw] at hbound
  rw [integral_add (integrable_const _) (hstep.const_mul _), integral_const,
    integral_const_mul] at hbound
  simp only [probReal_univ, one_smul] at hbound
  constructor
  · simpa only [hrec] using hfresh.1
  · simp_rw [hrec]
    change _ ≤ (1 - beta p) ^ 2 * (∫ ξ, ‖U (S ξ)‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) + _ + _
    linarith

end LongTails.Proofs.SurjectiveProxLinearExpectation
