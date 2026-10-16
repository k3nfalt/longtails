import LongTails.Setups.SampledCompositeSmoothConvex
import LongTails.Proofs.ProximalLinearDecayConvergence

namespace OracleTemplate.SampledComposite

open LongTails.Setups.SampledCompositeSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * ⌈72 * q.L * q.R ^ 2 / q.ε + 900 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 + 6 * q.Δ / q.ε⌉₊

theorem result :
    Convergence LongTails.Setups.SampledCompositeSmoothConvex.spec budget :=
  convergence

end OracleTemplate.SampledComposite
