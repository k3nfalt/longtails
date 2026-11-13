import LongTails.Setups.StretchedExponentialMarkovConvex
import LongTails.Proofs.StretchedExponentialLowerModel
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.StretchedExponentialMarkovConvexLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.StretchedExponentialMarkovConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊p.τ / 32 * (p.σ * p.R / (8 * p.ε)) ^ (p.α / (p.α - 1)) * (p.α * Real.log (p.σ * p.R / (8 * p.ε)) / (2 * (p.α - 1))) ^ (1 / p.γ)⌋₊

theorem result : NonConvergence LongTails.Setups.StretchedExponentialMarkovConvex.spec budget := by
  intro p hp A _ b hb
  apply StretchedExponentialLowerBound.exists_failure p hp A b
  have h := hb 0
  simpa only [budget, StretchedExponentialLowerBound.lower_budget_identity p hp] using h

end LongTails.Theorems.StretchedExponentialMarkovConvexLowerBound
