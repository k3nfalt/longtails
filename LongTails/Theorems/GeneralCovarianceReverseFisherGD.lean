import LongTails.Setups.GeneralCovarianceReverseFisher
import LongTails.Algorithms.GeneralCovarianceReverseFisherGD
import LongTails.Proofs.GeneralCovarianceReverseFisherConvergence

open OracleTemplate

namespace LongTails.Theorems.GeneralCovarianceReverseFisherGD

open LongTails.Setups.GeneralCovarianceReverseFisher
open LongTails.Algorithms.GeneralCovarianceReverseFisherGD
open LongTails.Proofs.GeneralCovarianceReverseFisherConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(1 + 8 * Real.log p.components) * (p.upper / p.lower) ^ 2 * (2 * Real.log (1 + p.radius ^ 2 / p.lower) + 4 * p.components * min (p.components : ℝ) p.dimension * p.upper / p.accuracy)⌉₊ + 1

theorem result : Convergence LongTails.Setups.GeneralCovarianceReverseFisher.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp M oracle ho
    have hb : budget p = fun _ => ⌈(1 + 8 * Real.log p.components) * (p.upper / p.lower) ^ 2 *
        (2 * Real.log (1 + p.radius ^ 2 / p.lower) +
          4 * p.components * min (p.components : ℝ) p.dimension * p.upper / p.accuracy)⌉₊ + 1 :=
      rfl
    rw [hb]
    refine output_success p hp M oracle ho _ ?_
    push_cast
    linarith [Nat.le_ceil ((1 + 8 * Real.log p.components) * (p.upper / p.lower) ^ 2 *
      (2 * Real.log (1 + p.radius ^ 2 / p.lower) +
        4 * p.components * min (p.components : ℝ) p.dimension * p.upper / p.accuracy))]
  · intro p hp
    exact algorithm_gdFamily p hp.1

end LongTails.Theorems.GeneralCovarianceReverseFisherGD
