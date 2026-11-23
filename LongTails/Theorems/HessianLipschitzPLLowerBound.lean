import LongTails.Setups.HighDimensionalHessianLipschitzPL
import LongTails.Proofs.HessianPLHardness
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.HessianLipschitzPLLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalHessianLipschitzPL.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊(q.H ^ 2 * q.Δ / q.μ ^ 3) ^ (1 / 4 : ℝ) / 2 ^ 39⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalHessianLipschitzPL.spec budget := by
  intro q hq A _ b hb
  exact LongTails.Proofs.HessianPLHardness.hard q hq A b (hb 0)

end LongTails.Theorems.HessianLipschitzPLLowerBound
