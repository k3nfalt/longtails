import LongTails.Setups.ManyConstraintStochasticConvex
import LongTails.Proofs.ManyConstraintConvergence

namespace OracleTemplate.PenaltyKatyushaManyConstraint

open LongTails.Setups.ManyConstraintStochasticConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q i => if i = 0 then 2 * q.m * ⌈(13 + 3264 * Real.sqrt (q.κ / q.m) * (q.σ * q.R / q.ε + q.R * Real.sqrt (q.L / q.ε))) * Real.log (50000 * q.κ * (1 + q.σ * q.R / q.ε + q.L * q.R ^ 2 / q.ε) ^ 2)⌉₊ * ⌈3 + 544 * (q.σ * q.R / q.ε + q.R * Real.sqrt (q.L / q.ε)) / Real.sqrt (q.m * q.κ)⌉₊ else ⌈q.κ * Real.log (4 * q.R ^ 2 / q.δ ^ 2)⌉₊ + 5 * q.m * ⌈(13 + 3264 * Real.sqrt (q.κ / q.m) * (q.σ * q.R / q.ε + q.R * Real.sqrt (q.L / q.ε))) * Real.log (50000 * q.κ * (1 + q.σ * q.R / q.ε + q.L * q.R ^ 2 / q.ε) ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.ManyConstraintStochasticConvex.spec budget :=
  LongTails.Proofs.ManyConstraintConvergence.convergence_main

end OracleTemplate.PenaltyKatyushaManyConstraint
