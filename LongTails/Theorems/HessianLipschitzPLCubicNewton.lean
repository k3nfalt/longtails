import LongTails.Setups.HessianLipschitzPL
import LongTails.Proofs.CubicNewtonPLConvergence

namespace LongTails.Theorems.HessianLipschitzPLCubicNewton

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HessianLipschitzPL.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈53 * (p.H ^ 2 * p.Δ / p.μ ^ 3) ^ (1 / 4 : ℝ) + 5 * Real.log (1 + Real.log (1 + p.μ ^ 3 / (p.H ^ 2 * p.ε))) + 4⌉₊

theorem result : Convergence LongTails.Setups.HessianLipschitzPL.spec budget :=
  LongTails.Proofs.CubicNewtonPLConvergence.convergence

end LongTails.Theorems.HessianLipschitzPLCubicNewton
