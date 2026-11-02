import LongTails.Setups.UscgVanishing
import LongTails.Proofs.UscgRates

namespace OracleTemplate.UscgVanishing

open LongTails.Setups.UscgVanishing

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈((2 * p.Δ / p.ρ + 8 / 3 * (p.ρ₂ / p.ρ + p.ζ) * Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.ρ₂ ^ 2) + p.L * p.ρ) / p.ε) ^ 4⌉₊ + 1

theorem result : Convergence LongTails.Setups.UscgVanishing.spec budget := by
  exact OracleTemplate.NormBallLMO.uscg_vanishing_convergence

end OracleTemplate.UscgVanishing
