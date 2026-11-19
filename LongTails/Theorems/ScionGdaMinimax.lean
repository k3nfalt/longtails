import LongTails.Setups.MinimaxLmo
import LongTails.Proofs.MinimaxLmoRate

namespace OracleTemplate.ScionGdaMinimax

open LongTails.Setups.MinimaxLmo

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 39 * (1 + p.L₀ / p.μ) * (1 + p.L₁ * p.ε / p.L₀ * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))))) ^ 4 * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1 + p.L₀ * p.W / p.ε + Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + p.ζ * p.σx / p.ε) * ((p.ζ * p.σx / p.ε) ^ 2 + (p.L₀ / p.μ) ^ 2 * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))) + (p.σy / p.ε) ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.MinimaxLmo.spec budget := by
  exact OracleTemplate.MinimaxLmo.minimax_lmo_convergence

end OracleTemplate.ScionGdaMinimax
