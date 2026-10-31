import LongTails.Setups.RelativeEnergySymmetricNonconvex
import LongTails.Proofs.FairConvergence

namespace LongTails.Theorems.FairRelativeEnergyNonconvex

open OracleTemplate
open OracleTemplate.FairVarianceReduction
open LongTails.Setups.RelativeEnergySymmetricNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(2 : ℝ) ^ 66 * (1 + Real.log (((q.r + q.ε) ^ 2 + q.L * q.Δ) / q.ε ^ 2)) * (((q.r + q.ε) ^ 2 + q.L * q.Δ) / q.ε ^ 2 + min (q.κ * q.ε) q.L * (q.r + q.ε) ^ 2 * q.Δ / q.ε ^ 4)⌉₊

theorem result : Convergence LongTails.Setups.RelativeEnergySymmetricNonconvex.spec budget := by
  refine ⟨fun q => algorithm (tunedConfig q.L q.κ q.r q.Δ q.ε) q.x0, ?_, ?_⟩
  · intro q hv f O hadm
    exact tuned_execute_accuracy q hv f O hadm (budget q 0)
      (tuned_calls_simplified hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2)
  · intro q hv
    trivial

end LongTails.Theorems.FairRelativeEnergyNonconvex
