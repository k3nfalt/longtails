import LongTails.Setups.ConstrainedGeneralizedMonotone
import LongTails.Proofs.ConstrainedAnchoredExecution

namespace OracleTemplate.ConstrainedMonotone

open LongTails.Setups.ConstrainedGeneralizedMonotone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q i => if i = 0 then 2 * (⌈16 * (q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R) * q.R / q.ε + (132 * q.L1 * q.R * (1 + q.L1 * q.R) + 4) * Real.log (2 + 8 * q.R * (q.L0 + 2 * q.L1 * q.G0) / q.ε)⌉₊ + 1) else ⌈16 * (q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R) * q.R / q.ε + (132 * q.L1 * q.R * (1 + q.L1 * q.R) + 4) * Real.log (2 + 8 * q.R * (q.L0 + 2 * q.L1 * q.G0) / q.ε)⌉₊ + 1

theorem result : Convergence LongTails.Setups.ConstrainedGeneralizedMonotone.spec budget :=
  convergence_main

end OracleTemplate.ConstrainedMonotone
