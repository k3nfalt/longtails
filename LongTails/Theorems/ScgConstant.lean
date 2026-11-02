import LongTails.Setups.ScgConstant
import LongTails.Proofs.ScgRates

namespace OracleTemplate.ScgConstant

open LongTails.Setups.ScgConstant

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈((p.Δ + 2 * p.L * p.ρ ^ 2 + (2 * p.L₂ * p.D₂ ^ 2 + 4 * p.D₂ * p.σ) / p.α) / p.ε) ^ 2⌉₊ + 1

theorem result : Convergence LongTails.Setups.ScgConstant.spec budget := by
  exact OracleTemplate.NormBallLMO.scg_constant_convergence

end OracleTemplate.ScgConstant
