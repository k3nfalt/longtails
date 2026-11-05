import LongTails.Setups.StrongGrowthFiniteSumSecondOrder
import LongTails.Proofs.Execution
import LongTails.Proofs.CoupledCubicBudget

namespace LongTails.Theorems.CoupledCubicStrongGrowth

open OracleTemplate
open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Algorithms.CoupledCubicTournament

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈10 ^ 20 * p.κ * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ)⌉₊ * (Nat.log 2 (3 * (⌈16000 * Real.sqrt p.ρ * p.Δ / (p.ε * Real.sqrt p.ε)⌉₊ + 1)) + 1) * (⌈16000 * Real.sqrt p.ρ * p.Δ / (p.ε * Real.sqrt p.ε)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.StrongGrowthFiniteSumSecondOrder.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => method p (batchSize p) (modelsPerRound p) (roundCount p), ?_, fun _ _ => trivial⟩
  intro p hv f O hadm
  apply LongTails.Proofs.CoupledCubicBudget.method_success p hv f O hadm (budget p 0)
  simp [budget, batchSize, modelsPerRound, roundCount]

end LongTails.Theorems.CoupledCubicStrongGrowth
