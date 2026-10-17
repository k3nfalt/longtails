import LongTails.Setups.ExpectedSmoothnessNonconvex
import LongTails.Proofs.NormalizedStormConvergence

namespace OracleTemplate.NormalizedStorm

open LongTails.Setups.ExpectedSmoothnessNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(192 * (4 * q.A * q.Δ + q.C) + 80 * q.L * q.Δ) / q.ε ^ 2 + 384 * q.A / q.L + 1600 * q.L * q.Δ * Real.sqrt (4 * q.A * q.Δ + 2 * q.A * q.ε ^ 2 / q.L + q.C) / q.ε ^ 3⌉₊ + 3

theorem result : Convergence LongTails.Setups.ExpectedSmoothnessNonconvex.spec budget :=
  convergence

end OracleTemplate.NormalizedStorm
