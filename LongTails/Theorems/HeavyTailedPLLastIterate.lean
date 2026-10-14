import LongTails.Setups.HeavyTailedPL
import LongTails.Proofs.HeavyTailedPLConvergence

namespace OracleTemplate.HeavyTailedPL

open LongTails.Setups.HeavyTailedPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈44 * (p.L / p.μ) * Real.sqrt (p.Δ / p.ε) + 1024 * p.σ ^ 2 * (p.L / p.μ + Real.log (3 / p.δ)) / (p.μ * p.ε) + ((64 * (p.L / p.μ) ^ 2 * (p.ν / p.σ) ^ 2 * Real.log (3 / p.δ)) ^ p.q * (3 / p.δ) ^ 2) ^ (1 / (p.q - 2))⌉₊

theorem result : Convergence LongTails.Setups.HeavyTailedPL.spec budget := convergence

end OracleTemplate.HeavyTailedPL
