import LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex
import LongTails.Proofs.ProximalStormConvergence

namespace OracleTemplate.ProximalStorm

open LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈Real.sqrt (2 * q.Lbar * q.R ^ 2 / ((1 + q.Γ) * q.ε))⌉₊ * ⌈(1 + q.Γ) ^ 2 * (4810 + 3200 * Real.log (1 + q.Γ))⌉₊

theorem result : Convergence LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex.spec budget :=
  convergence

end OracleTemplate.ProximalStorm
