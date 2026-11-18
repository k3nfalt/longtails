import LongTails.Setups.CorruptedFirstOrderNonconvex

open OracleTemplate

namespace LongTails.Setups.CorruptedFirstOrderNonconvex.HighDimensional

abbrev spec : Setup := { CorruptedFirstOrderNonconvex.spec with
  valid := fun (p : Params) => 0 < p.L ∧ 0 < p.ε ∧ 2 ^ 26 * p.ε ^ 2 ≤ p.L * p.Δ ∧
    2 ^ 32 * (⌊p.L * p.Δ / (2 ^ 25 * p.ε ^ 2)⌋₊ + 1) ^ 4 ≤ p.d }

end LongTails.Setups.CorruptedFirstOrderNonconvex.HighDimensional
