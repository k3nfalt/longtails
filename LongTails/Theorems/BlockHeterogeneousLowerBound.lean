import LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex
import LongTails.Proofs.BlockLowerParameters
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.BlockHeterogeneousLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊((∑ j, q.L j) * q.Δ / q.ε ^ 2 + (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4) / 2 ^ 57⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex.spec budget := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨a, hav⟩ := LongTails.Proofs.BlockLowerParameters.exists_alloc q hv (b 0) (hb 0)
  obtain ⟨w, hw⟩ := LongTails.Proofs.BlockLowerBound.exists_failure hav hv.2.2.2.1 A
  exact ⟨_, _, LongTails.Proofs.BlockLowerInstance.hard_admissible hav w, hw⟩

end LongTails.Theorems.BlockHeterogeneousLowerBound
