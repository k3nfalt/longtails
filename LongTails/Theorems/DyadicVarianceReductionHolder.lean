import LongTails.Setups.MeanSquaredHolderNonconvex
import LongTails.Proofs.DyadicHolderConvergence

namespace OracleTemplate.DyadicHolder

open LongTails.Setups.MeanSquaredHolderNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈800 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 * (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.Δ * q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν) / q.ε ^ 3)⌉₊

theorem result : Convergence LongTails.Setups.MeanSquaredHolderNonconvex.spec budget :=
  convergence

end OracleTemplate.DyadicHolder
