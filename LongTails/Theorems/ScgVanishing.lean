import LongTails.Setups.ScgVanishing
import LongTails.Proofs.ScgRates

namespace OracleTemplate.ScgVanishing

open LongTails.Setups.ScgVanishing

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈((2 * p.Δ + 4 / 3 * p.D₂ * Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.D₂ ^ 2) + 2 * p.L * p.ρ ^ 2) / p.ε) ^ 4⌉₊ + 1

theorem result : Convergence LongTails.Setups.ScgVanishing.spec budget := by
  exact OracleTemplate.NormBallLMO.scg_vanishing_convergence

end OracleTemplate.ScgVanishing
