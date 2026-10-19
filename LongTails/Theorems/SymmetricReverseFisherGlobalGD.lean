import LongTails.Setups.SymmetricGaussianReverseFisher
import LongTails.Algorithms.SymmetricReverseFisherGD
import LongTails.Proofs.SymmetricReverseFisherConvergence

open OracleTemplate

namespace LongTails.Theorems.SymmetricReverseFisherGlobalGD

open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Algorithms.SymmetricReverseFisherGD
open LongTails.Proofs.SymmetricReverseFisherBudget
open LongTails.Proofs.SymmetricReverseFisherExecution
open LongTails.Proofs.SymmetricReverseFisherConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈1000000000000000 * (1 + p.upper) * (1 + p.lower ^ 2) / max (p.lower ^ 2) p.accuracy * Real.log (1000000000000000 * p.dimension * (1 + p.upper) / (p.failure * p.accuracy))⌉₊

theorem result : Convergence LongTails.Setups.SymmetricGaussianReverseFisher.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp μ oracle ho
    have hb : budget p = fun _ => iterations p.dimension p.lower p.upper p.failure p.accuracy := by
      funext i
      exact (iterations_formula p.dimension p.lower p.upper p.failure p.accuracy).symm
    rw [hb]
    exact output_success p hp μ oracle ho
  · intro p hp
    exact algorithm_gdFamily p (hp.1.trans hp.2.1)

end LongTails.Theorems.SymmetricReverseFisherGlobalGD
