import LongTails.Setups.MomentumLipschitzConvex
import LongTails.Proofs.MomentumLastIterateConvergence

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈100 * q.G ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊ + ⌈4 * (q.β / (1 - q.β)) ^ 2 * (1 + Real.log (1 / (1 - q.β)))⌉₊

theorem result : Convergence LongTails.Setups.MomentumLipschitzConvex.spec budget :=
  convergence

end OracleTemplate.MomentumConvex
