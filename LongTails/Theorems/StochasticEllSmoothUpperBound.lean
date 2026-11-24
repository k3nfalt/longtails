import LongTails.Setups.StochasticEllSmoothNonconvex
import LongTails.Proofs.StochasticEllSmoothUpper

open OracleTemplate

namespace LongTails.Theorems.StochasticEllSmoothUpperBound

noncomputable def budget : (let S := LongTails.Setups.StochasticEllSmoothNonconvex.spec;
    S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let T := q.Δ * q.ℓ q.ε / q.ε ^ 2
  let r := q.p / (q.p - 1)
  ⌈2 ^ 15 * (1 + T) * (1 + (2 ^ 16 * q.σ / q.ε) ^ r) * Real.logb 2 (2 + T) / (2 - q.ρ)⌉₊

theorem result : Convergence LongTails.Setups.StochasticEllSmoothNonconvex.spec budget :=
  LongTails.Proofs.StochasticEllSmoothUpper.convergence

end LongTails.Theorems.StochasticEllSmoothUpperBound
