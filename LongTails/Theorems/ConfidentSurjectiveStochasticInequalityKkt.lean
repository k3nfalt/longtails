import LongTails.Setups.ConfidentStochasticSurjectiveInequalities
import LongTails.Algorithms.SurjectiveConfidence
import LongTails.Proofs.SurjectiveConfidenceConvergence
import LongTails.Proofs.SurjectiveConfidenceBudget

namespace LongTails.Theorems.ConfidentSurjectiveStochasticInequalityKkt

open OracleTemplate
open LongTails.Setups.ConfidentStochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveConfidence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 * Real.log (2 / p.δ) + 2) * (70 + (2 ^ 29 * p.problem.m ^ 2 * p.problem.H ^ 10 * p.problem.Δ + 2 ^ 44 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2) / p.problem.ε ^ 2 + 2 ^ 48 * p.problem.m ^ 4 * p.problem.H ^ 19 * p.problem.Δ * p.problem.σ / p.problem.ε ^ 3 + (8 * Real.log (2 / p.δ) + 2) * (2 + 2 ^ 40 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2 / p.problem.ε ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.ConfidentStochasticSurjectiveInequalities.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp I oracle hadm
    exact LongTails.Proofs.SurjectiveConfidenceConvergence.execution_success p hp I oracle hadm _
      (LongTails.Proofs.SurjectiveConfidenceBudget.total_call_budget p hp)
  · intro p hp
    trivial

end LongTails.Theorems.ConfidentSurjectiveStochasticInequalityKkt
