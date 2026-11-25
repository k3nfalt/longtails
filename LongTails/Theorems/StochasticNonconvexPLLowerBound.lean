import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalStochasticNonconvexPL
import LongTails.Proofs.NcPlFailure

namespace LongTails.Theorems.StochasticNonconvexPLLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalStochasticNonconvexPL.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) * (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2))⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalStochasticNonconvexPL.spec budget := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨π, hπ⟩ := LongTails.Proofs.NcPlFailure.exists_failure hv A (b 0) (hb 0)
  exact ⟨_, _, LongTails.Proofs.NcPlLowerBound.hard_admissible hv π, hπ⟩

end LongTails.Theorems.StochasticNonconvexPLLowerBound
