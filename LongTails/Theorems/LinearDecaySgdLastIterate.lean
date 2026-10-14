import LongTails.Setups.SampledSmoothConvex
import LongTails.Proofs.LinearDecaySgdConvergence

namespace OracleTemplate.SampledConvex

open LongTails.Setups.SampledSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈48 * q.L * q.R ^ 2 / q.ε + 324 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem result :
    Convergence LongTails.Setups.SampledSmoothConvex.spec budget :=
  convergence

end OracleTemplate.SampledConvex
