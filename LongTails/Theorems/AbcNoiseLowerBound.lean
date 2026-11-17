import LongTails.Setups.HighDimensionalAbcNoiseNonconvex
import LongTails.Proofs.AbcLowerBound
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.AbcNoiseLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / (2 ^ 53 * q.ε ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec budget := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨π, hπ⟩ := LongTails.Proofs.AbcLowerBound.exists_failure q hv A (b 0) (hb 0)
  exact ⟨_, _, LongTails.Proofs.AbcLowerAssembly.hard_admissible q hv π, hπ⟩

end LongTails.Theorems.AbcNoiseLowerBound
