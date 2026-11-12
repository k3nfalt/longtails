import LongTails.Setups.SmoothFiniteMaximum
import LongTails.Algorithms.AffineResidualFiniteMaximum
import LongTails.Proofs.AffineResidualFiniteMaximum
import LongTails.Proofs.AffineResidualPublicBudget

namespace OracleTemplate.AffineResidualFiniteMaximum

open LongTails.Setups.SmoothFiniteMaximum

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (1 + Nat.clog 2 (Nat.ceil (1 / p.δ))) * Nat.ceil (10000000000000000000000 * ((1 + Nat.clog 2 (Nat.ceil (2 + (p.m : ℝ) + p.G * p.R / p.ε + p.L * p.R ^ 2 / p.ε)) : ℕ) : ℝ) ^ 8 * ((p.m : ℝ) + p.m * (p.L * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) + (p.m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (p.L * p.R ^ 2 / p.ε) + (p.L * p.R ^ 2 / p.ε) ^ (2 / 3 : ℝ)))

theorem result : Convergence LongTails.Setups.SmoothFiniteMaximum.spec budget := by
  refine ⟨LongTails.Algorithms.AffineResidualFiniteMaximum.algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I oracle ha
  apply LongTails.Proofs.AffineResidualFiniteMaximum.successful_execution p hp I oracle ha
  exact Nat.mul_le_mul_left (1 + Nat.clog 2 (Nat.ceil (1 / p.δ)))
    (LongTails.Proofs.AffineResidualPublicBudget.trial_budget_le p.hm hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1)

end OracleTemplate.AffineResidualFiniteMaximum
