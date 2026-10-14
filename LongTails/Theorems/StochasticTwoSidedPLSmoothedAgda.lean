import LongTails.Setups.StochasticTwoSidedPL
import LongTails.Proofs.TwoSidedPLConvergence

namespace OracleTemplate.StochasticTwoSidedPL

open LongTails.Setups.StochasticTwoSidedPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 4 * ⌈2 ^ 18 * p.L ^ 2 / (p.μx * p.μy) * (3 + 2 ^ 24 * p.L * p.σ ^ 2 / (p.μx * p.μy * p.ε)) * (2 + Real.log (1 + p.Δ / p.ε))⌉₊ + 2

theorem result : Convergence LongTails.Setups.StochasticTwoSidedPL.spec budget := by
  have hb : budget = fun p _ => 2 * (2 * windowLength p + 1) := by
    funext p i
    unfold budget windowLength
    ring
  rw [hb]
  exact convergence

end OracleTemplate.StochasticTwoSidedPL
