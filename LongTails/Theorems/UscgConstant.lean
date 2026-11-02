import LongTails.Setups.UscgConstant
import LongTails.Proofs.UscgRates

namespace OracleTemplate.UscgConstant

open LongTails.Setups.UscgConstant

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈((p.Δ / p.ρ + p.L * p.ρ / 2 + (p.ρ₂ / p.ρ + p.ζ) * (2 * p.L₂ * p.ρ₂ + 4 * p.σ) / p.α) / p.ε) ^ 2⌉₊ + 1

theorem result : Convergence LongTails.Setups.UscgConstant.spec budget := by
  exact OracleTemplate.NormBallLMO.uscg_constant_convergence

end OracleTemplate.UscgConstant
