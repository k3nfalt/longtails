import LongTails.Setups.StochasticPowerSmoothFixedPoint
import LongTails.Proofs.PowerSmoothAnchoringConvergence
import LongTails.Proofs.PowerSmoothAnchoringBudget

namespace LongTails.Theorems.PowerSmoothAnchoring

open OracleTemplate LongTails.Setups.StochasticPowerSmoothFixedPoint

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈512 * (1 + q.D / q.ε + (65536 * q.K * (q.σ / q.ε) ^ q.exponent) ^ (1 / (q.exponent - 1))) * (3 + Real.logb 2 (1 + 16 * q.D / q.ε)) ^ (2 + q.exponent / (q.exponent - 1))⌉₊

theorem result : Convergence LongTails.Setups.StochasticPowerSmoothFixedPoint.spec budget := by
  apply LongTails.Proofs.PowerSmoothAnchoringConvergence.convergence_of_budget
  rintro q ⟨hs, _, hK, hD, hσ, hε⟩
  exact LongTails.Proofs.PowerSmoothAnchoringBudget.total_steps_bound q hs
    (le_trans (by norm_num) hK) hD.le hσ hε

end LongTails.Theorems.PowerSmoothAnchoring
