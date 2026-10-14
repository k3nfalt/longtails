import LongTails.Setups.ReshuffledSmoothConvex
import LongTails.Proofs.ReshuffledExecution

namespace OracleTemplate.ReshuffledConvex

open LongTails.Setups.ReshuffledSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * ⌈384 * Real.sqrt (p.Lavg * p.Lmax) * p.R ^ 2 / p.ε + 30 * p.σ * p.R ^ 2 * Real.sqrt (p.Lavg / (p.n * p.ε ^ 3))⌉₊

theorem result : Convergence LongTails.Setups.ReshuffledSmoothConvex.spec budget :=
  convergence

end OracleTemplate.ReshuffledConvex
