import LongTails.Setups.StochasticFixedPointSmoothBanach
import LongTails.Proofs.RecursiveAnchorKmConvergence

namespace OracleTemplate.RecursiveAnchorKm

open LongTails.Setups.StochasticFixedPointSmoothBanach

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(Real.logb 2 (1 + q.D / q.ε) + 4) * (16 + 20 * q.D / q.ε + 2048 * q.K * q.σ ^ 2 * (Real.logb 2 (1 + q.D / q.ε) + 4) ^ 2 / q.ε ^ 2)⌉₊

theorem result :
    Convergence LongTails.Setups.StochasticFixedPointSmoothBanach.spec budget :=
  convergence

end OracleTemplate.RecursiveAnchorKm
