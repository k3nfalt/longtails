import LongTails.Proofs.SurjectiveProxLinearProbability
import LongTails.Proofs.SurjectiveProxLinearExecution

open MeasureTheory

namespace LongTails.Proofs.SurjectiveProxLinearConvergence

open OracleTemplate
open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearSampling
open LongTails.Proofs.SurjectiveProxLinearExecution
open LongTails.Proofs.SurjectiveProxLinearProbability

lemma execution_success (p : Params) (hp : spec.valid p) (I : Problem p)
    (oracle : Oracle (p.E × p.E) (Primitive p × Primitive p))
    (hadm : spec.admissible p I oracle) (K : ℕ)
    (hK : initialBatch p + iterations p + certificateBatch p ≤ K) :
    spec.successful p I
      (fun seed : (algorithm p).Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle (algorithm p) (fun _ => K) seed.1 seed.2)
      ⟨((algorithm p).law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  obtain ⟨g, v, D, μ, P, hIID, rfl, H, O⟩ := hadm
  have hP : (P : Measure (ℕ → p.Ω)) = Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω) := by
    have h := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → p.Ω)))).symm.trans h
  let Z := jointOracle p g v D
  have hout :
      (fun seed : (algorithm p).Seed × (ℕ → p.Ω) =>
        execute ({ Seed := fun _ => p.Ω
                   law := P
                   answer := fun _ (_, z) ω =>
                     ((g z.1 ω, v z.1 ω, D z.1 ω), (g z.2 ω, v z.2 ω, D z.2 ω)) } :
          Oracle (p.E × p.E) (Primitive p × Primitive p))
          (algorithm p) (fun _ => K) seed.1 seed.2) =
      (fun z : Fin (iterations p + 1) × (ℕ → p.Ω) =>
        ((trajectory p Z z.2 z.1.val).1,
          dualPoint p ((jointEquiv p).symm (certificateEstimator p Z z.2 z.1.val)))) := by
    funext seed
    exact execute_selected p (fun x ω => (g x ω, v x ω, D x ω)) P K seed.1 seed.2 hK
  change Measurable _ ∧ _
  rw [hout]
  refine ⟨selected_output_measurable p hp Z (jointOracle_measurable p I g v D μ O), ?_⟩
  change ENNReal.ofReal (3 / 4) ≤
    ((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod (P : Measure (ℕ → p.Ω))) _
  rw [hP]
  exact selected_output_success p I hp H g v D μ O

end LongTails.Proofs.SurjectiveProxLinearConvergence
