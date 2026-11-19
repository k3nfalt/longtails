import LongTails.Setups.HighDimensionalSeparableNoiseLinfSmooth
import LongTails.Proofs.LinfLowerTransfer
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.SeparableNoiseLinfSmoothLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalSeparableNoiseLinfSmooth.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) / (2 ^ 60 * q.ε ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalSeparableNoiseLinfSmooth.spec budget := by
  intro q hv A _ b hb
  exact LongTails.Proofs.LinfLowerTransfer.exists_failure q hv A b hb

end LongTails.Theorems.SeparableNoiseLinfSmoothLowerBound
