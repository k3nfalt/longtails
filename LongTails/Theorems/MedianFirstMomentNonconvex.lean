import LongTails.Setups.SymmetricFirstMomentNonconvex
import LongTails.Proofs.MedianConvergence

namespace OracleTemplate.MedianGradient

open LongTails.Setups.SymmetricFirstMomentNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 3 * ⌈14400 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 * (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.Λ * q.σ * q.Δ / q.ε ^ 3)⌉₊

theorem result : Convergence LongTails.Setups.SymmetricFirstMomentNonconvex.spec budget :=
  convergence

end OracleTemplate.MedianGradient
