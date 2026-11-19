import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalStochasticWeakMinty
import LongTails.Proofs.StochasticMintyLowerBound

namespace LongTails.Theorems.StochasticWeakMintyLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalStochasticWeakMinty.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.L ^ 2 * q.R ^ 2 * (q.ε ^ 2 + q.σ ^ 2) / (2 ^ 19 * q.ε ^ 4)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalStochasticWeakMinty.spec budget := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨π, hπ⟩ := LongTails.Proofs.StochasticMintyLowerBound.exists_failure q hv A (b 0) (hb 0)
  exact ⟨_, _, LongTails.Proofs.StochasticMintyLowerBound.hard_admissible q hv π, hπ⟩

end LongTails.Theorems.StochasticWeakMintyLowerBound
