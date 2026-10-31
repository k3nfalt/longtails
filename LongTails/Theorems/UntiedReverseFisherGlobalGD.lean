import LongTails.Setups.UntiedGaussianReverseFisher
import LongTails.Algorithms.UntiedReverseFisherGD
import LongTails.Proofs.UntiedReverseFisherConvergence

open OracleTemplate

namespace LongTails.Theorems.UntiedReverseFisherGlobalGD

open LongTails.Setups.UntiedGaussianReverseFisher
open LongTails.Algorithms.UntiedReverseFisherGD
open LongTails.Proofs.UntiedReverseFisherBudget
open LongTails.Proofs.UntiedReverseFisherExecution
open LongTails.Proofs.UntiedReverseFisherConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈10 ^ 16 / max (p.lower ^ 2) p.accuracy * Real.log (10 ^ 20 * p.dimension * (1 + p.centre) / (p.failure * p.accuracy))⌉₊

theorem result : Convergence LongTails.Setups.UntiedGaussianReverseFisher.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp μ oracle ho
    have hb : budget p = fun _ => iterations p.dimension p.lower p.centre p.failure p.accuracy := by
      funext i
      rfl
    rw [hb]
    exact output_success p hp μ oracle ho
  · intro p _
    exact algorithm_constantStepGD p

end LongTails.Theorems.UntiedReverseFisherGlobalGD
