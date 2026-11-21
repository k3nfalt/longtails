import LongTails.Setups.EuclideanWeakMinty

namespace LongTails.Setups.FiniteDimensionalWeakMinty

open OracleTemplate

abbrev Params := EuclideanWeakMinty.Params

abbrev spec : Setup := { EuclideanWeakMinty.spec with
  valid := fun p => 0 < p.d ∧ 0 < p.L ∧ 0 ≤ p.ρ ∧ p.ρ ≤ 1 / (20 * p.L) ∧
    0 < p.ε ∧ p.ε < p.L * p.R }

end LongTails.Setups.FiniteDimensionalWeakMinty
