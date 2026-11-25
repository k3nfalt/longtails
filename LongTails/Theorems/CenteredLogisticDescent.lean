import LongTails.Setups.CenteredLogisticClassification
import LongTails.Proofs.CenteredLogisticExecution

open OracleTemplate

namespace LongTails.Theorems.CenteredLogisticDescent

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Proofs.CenteredLogisticExecution

def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * p.n

theorem result : Convergence LongTails.Setups.CenteredLogisticClassification.spec budget := by
  refine ⟨LongTails.Algorithms.CenteredLogisticDescent.algorithm, ?_, fun p _ => algorithm_family p⟩
  intro p _ D O h
  obtain ⟨⟨G⟩, ho⟩ := h
  dsimp only
  intro ω i
  exact output_positive p D G O ho ω.1 ω.2 i

end LongTails.Theorems.CenteredLogisticDescent
