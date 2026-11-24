import LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex
import LongTails.Proofs.StochasticEllSmoothLower

open OracleTemplate

namespace LongTails.Theorems.StochasticEllSmoothLowerBound

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex.spec;
    S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let T := q.Δ * q.ℓ q.ε / q.ε ^ 2
  let r := q.p / (q.p - 1)
  ⌊(2 - q.ρ) * T * max 1 ((q.σ / (2 ^ 13 * q.ε)) ^ r) / 2 ^ 32⌋₊

theorem result :
    NonConvergence LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex.spec budget := by
  intro q hq A _ b hb
  have heq : b = fun _ => b 0 := by funext i; rw [Subsingleton.elim i 0]
  rw [heq]
  obtain ⟨π, hπ⟩ := LongTails.Proofs.StochasticEllSmoothLower.exists_failure q hq A (b 0) (hb 0)
  exact ⟨_, _, LongTails.Proofs.StochasticEllSmoothLower.hard_admissible q hq π, hπ⟩

end LongTails.Theorems.StochasticEllSmoothLowerBound
