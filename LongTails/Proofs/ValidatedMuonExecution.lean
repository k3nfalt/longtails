import LongTails.Algorithms.ValidatedMuon
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.MuonTrainingSimulation
import LongTails.Proofs.MuonValidationSimulation

namespace LongTails.Proofs.ValidatedMuonExecution

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon

lemma execute_validatedMuon {Ω : Type} [MeasurableSpace Ω] {m n : ℕ}
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    (α η ρ : ℝ) (T b k q K : ℕ) (x0 : Space m n)
    (seed : Fin (q + 1) → Fin (T + 1)) (ξ : ℕ → Ω)
    (hK : (b * (k + 1)) * (q + 1) + (T + 1) ≤ K) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (validatedMuon α η ρ T b k q x0) (fun _ => K) seed ξ =
      QueryPlan.sampledEval g ξ
        (validationPlan ρ b k q (fun i =>
          (QueryPlan.sampledEval g ξ (trainingPlan α η (T + 1) x0 0) 0) (seed i)))
        (T + 1) := by
  let C := (b * (k + 1)) * (q + 1)
  let extra := K - ((T + 1) + C)
  have hbudget : K = T + 1 + (C + extra) := by
    dsimp [C, extra]
    omega
  erw [MuonSimulation.execute_validatedMuon_resume]
  rw [hbudget]
  rw [MuonSimulation.sampledEval_training_resume α η ρ x0 g ξ seed extra 0]
  exact MuonValidationSimulation.sampledEval_resumeMuonPlan_validation
    α η ρ b k q extra x0 g ξ (fun i =>
      (QueryPlan.sampledEval g ξ (trainingPlan α η (T + 1) x0 0) 0) (seed i)) (T + 1)

end LongTails.Proofs.ValidatedMuonExecution
