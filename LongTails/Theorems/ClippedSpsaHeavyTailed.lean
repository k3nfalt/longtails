import LongTails.Setups.HeavyTailedTwoPointZerothOrder
import LongTails.Proofs.SpsaConvergence

namespace OracleTemplate.ClippedSpsaHeavyTailed

open LongTails.Setups.HeavyTailedTwoPointZerothOrder

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 20 * 132 ^ (q.p / (q.p - 1)) * q.L * q.d * q.Δ / q.ε ^ 2 * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1)))⌉₊ + 1

theorem result : Convergence LongTails.Setups.HeavyTailedTwoPointZerothOrder.spec budget :=
  LongTails.Proofs.SpsaConvergence.convergence

end OracleTemplate.ClippedSpsaHeavyTailed
