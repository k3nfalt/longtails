import LongTails.Setups.CurvatureAlignedNoiseNonconvex
import LongTails.Proofs.CurvatureAlignedConvergence

namespace OracleTemplate.CurvatureAligned

open LongTails.Setups.CurvatureAlignedNoiseNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈4 * q.Lg * q.Δ / q.ε ^ 2 + 8 * q.Lξ * q.σ ^ 2 * q.Δ / q.ε ^ 4⌉₊ + 1

theorem result : Convergence LongTails.Setups.CurvatureAlignedNoiseNonconvex.spec budget :=
  convergence

end OracleTemplate.CurvatureAligned
