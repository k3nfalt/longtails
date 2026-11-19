import LongTails.Setups.FlatTransferDueling
import LongTails.Proofs.DuelingReferenceLowerBound

open OracleTemplate
open LongTails.Proofs.DuelingSignFamily (loss scale)
open LongTails.Proofs.DuelingTestingExecution (oracle)
open LongTails.Proofs.DuelingSignOracle (chance admissible)
open LongTails.Proofs.DuelingReferenceLowerBound (exists_bad testing_budget)

namespace LongTails.Theorems.LocalReferenceDuelingLowerBound

noncomputable def budget : (let S := LongTails.Setups.FlatTransferDueling.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(p.d : ℝ)^2 / (65536 * (2*(p.j : ℝ)+1)^2 * p.ε^2)⌋₊

theorem result : NonConvergence LongTails.Setups.FlatTransferDueling.spec budget := by
  intro p hp A _ b hb
  obtain ⟨θ, hfail⟩ := exists_bad hp A (b 0) (testing_budget hp.1 (hb 0))
  refine ⟨loss (scale p) θ, oracle (chance p θ), admissible hp θ, ?_⟩
  have h : (fun _ : Fin 1 => b 0) = b := funext fun i => congrArg b (Subsingleton.elim _ i)
  rw [h] at hfail
  exact hfail

end LongTails.Theorems.LocalReferenceDuelingLowerBound
