import LongTails.Setups.SlidingGeneralizedSmooth
import LongTails.Proofs.SlidingConvergence

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q i => if i = 0 then 2 * ⌈20 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (6 + 320 * q.L1 * q.R) * Real.log (2 + (3 + 240 * q.L1 * q.R) * Real.sqrt (q.Δ / (q.L0 * q.R ^ 2)))⌉₊ else 8 * ⌈20 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (6 + 320 * q.L1 * q.R) * Real.log (2 + (3 + 240 * q.L1 * q.R) * Real.sqrt (q.Δ / (q.L0 * q.R ^ 2)))⌉₊ + ⌈768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.SlidingGeneralizedSmooth.spec budget :=
  convergence_main

end OracleTemplate.GeneralizedSliding
