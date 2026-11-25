import LongTails.Setups.StochasticNonconvexPL
import LongTails.Proofs.NonconvexPLUpper

namespace LongTails.Theorems.StochasticNonconvexPLUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.StochasticNonconvexPL.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * ⌈2 ^ 44 * p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2) * (1 + p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.StochasticNonconvexPL.spec budget :=
  OracleTemplate.StochasticNonconvexPL.convergence

end LongTails.Theorems.StochasticNonconvexPLUpperBound
