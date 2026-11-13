import LongTails.Setups.SublevelPLBoundedVariance
import LongTails.Proofs.SublevelPLResult

namespace OracleTemplate.SublevelRobustGradient.SublevelPLRobustBatchedGd

open LongTails.Setups.SublevelPLBoundedVariance

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌈32 * p.α / (7 * (2 - p.α)) * p.L * p.τ ^ (2 / p.α) * (p.ε / 4) ^ (-(2 - p.α) / p.α)⌉₊ + 1) * ((6 + ⌈Real.logb 2 (32 * (32 * p.α / (7 * (2 - p.α)) * p.L * p.τ ^ (2 / p.α) * (p.ε / 4) ^ (-(2 - p.α) / p.α) + 2) * p.Δ / p.ε)⌉₊) * (1 + ⌈(1152 + 16 * (6 + ⌈Real.logb 2 (32 * (32 * p.α / (7 * (2 - p.α)) * p.L * p.τ ^ (2 / p.α) * (p.ε / 4) ^ (-(2 - p.α) / p.α) + 2) * p.Δ / p.ε)⌉₊)) * (19 * p.α / (2 - p.α) * p.τ ^ (2 / p.α) * p.σ ^ 2 * p.ε ^ (-(2 / p.α)) + 2 * p.σ ^ 2 / (p.L * p.ε))⌉₊))

theorem result : Convergence LongTails.Setups.SublevelPLBoundedVariance.spec budget := by
  have h : budget = fun p _ => steps p.L p.τ p.α p.ε *
      (subbatches p.L p.τ p.α p.Δ p.ε * subsize p.L p.τ p.α p.σ p.Δ p.ε) := by
    funext p i
    simp only [budget, steps, subbatches, subsize, rate, noise]
    push_cast
    ring_nf
  rw [h]
  exact convergence

end OracleTemplate.SublevelRobustGradient.SublevelPLRobustBatchedGd
