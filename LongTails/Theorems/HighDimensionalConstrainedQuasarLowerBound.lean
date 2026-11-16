import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalConstrainedQuasar
import LongTails.Proofs.QuasarLowerAssembly

namespace LongTails.Theorems.HighDimensionalConstrainedQuasarLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalConstrainedQuasar.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊Real.sqrt (q.L * q.D ^ 2 / q.ε) / (10000 * q.γ) + q.σ ^ 2 * q.D ^ 2 * Real.log (1 / q.δ) / (8192 * q.γ ^ 2 * q.ε ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalConstrainedQuasar.spec budget := by
  intro p hv A _ b hb
  exact LongTails.Proofs.QuasarLowerAssembly.lower_failure p hv A b hb

end LongTails.Theorems.HighDimensionalConstrainedQuasarLowerBound
