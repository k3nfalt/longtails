import LongTails.Setups.AbcNoiseNonconvex
import LongTails.Proofs.AbcSgdConvergence

namespace LongTails.Theorems.AbcNoiseSgdUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.AbcNoiseNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈144 * q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2⌉₊ + 1

theorem result : Convergence LongTails.Setups.AbcNoiseNonconvex.spec budget :=
  LongTails.Proofs.AbcSgdConvergence.sgd_convergence

end LongTails.Theorems.AbcNoiseSgdUpperBound
