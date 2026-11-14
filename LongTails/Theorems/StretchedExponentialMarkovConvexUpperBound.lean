import LongTails.Setups.StretchedExponentialMarkovConvex
import LongTails.Proofs.StretchedExponentialUpper

namespace LongTails.Theorems.StretchedExponentialMarkovConvexUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.StretchedExponentialMarkovConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈Real.sqrt (32 * p.L * p.R ^ 2 / p.ε) + (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))⌉₊ * ⌈Real.exp 1 * p.τ * (Real.log (256 * p.L * p.R ^ 2 / p.ε + 64 * (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))) / p.γ) ^ (1 / p.γ)⌉₊

theorem result : Convergence LongTails.Setups.StretchedExponentialMarkovConvex.spec budget := by
  apply StretchedExponentialUpperBound.transfer (fun p => budget p 0)
  intro p hp
  funext i
  exact StretchedExponentialUpperBound.inherited_budget_simplified p hp i

end LongTails.Theorems.StretchedExponentialMarkovConvexUpperBound
