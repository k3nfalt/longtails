import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalStrongQuasar
import LongTails.Proofs.StrongQuasarChainLowerBound

namespace LongTails.Theorems.HighDimensionalStrongQuasarLowerBound

open OracleTemplate LongTails.Proofs.StrongQuasarChainLowerBound
open LongTails.Proofs.StrongQuasarChainParameters

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalStrongQuasar.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊Real.sqrt (p.L / p.μ) / (8000 * p.γ)⌋₊ * Nat.log 2 ⌊p.Δ / (1000 * p.γ * Real.sqrt (p.L / p.μ) * p.ε)⌋₊ / 2

theorem result : NonConvergence LongTails.Setups.HighDimensionalStrongQuasar.spec budget := by
  intro p hp A _ b hb
  have hb0 : b 0 ≤ lowerBudget p := hb 0
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact exists_failure hp (b 0) hb0 A

end LongTails.Theorems.HighDimensionalStrongQuasarLowerBound
