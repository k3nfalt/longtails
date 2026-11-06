import LongTails.Setups.CovarianceSmoothConvex
import LongTails.Proofs.CovarianceAcceleratedSpecification

namespace LongTails.Theorems.CovarianceAcceleratedHighProbability

open LongTails.Setups.CovarianceSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(2 : ℝ)^40*((Real.log ((2 : ℝ)^56*(1+q.L*q.R^2/q.ε+q.R^2*q.σ^2/q.ε^2)/q.δ^2))^2+Real.sqrt (q.L*q.R^2/q.ε)*Real.log ((2 : ℝ)^56*(1+q.L*q.R^2/q.ε+q.R^2*q.σ^2/q.ε^2)/q.δ^2)+q.R^2*(q.σ^2+q.s^2*Real.log (3/q.δ))/q.ε^2)⌉₊

theorem result : OracleTemplate.Convergence LongTails.Setups.CovarianceSmoothConvex.spec budget := by
  refine ⟨fun q => LongTails.Algorithms.CovarianceAcceleratedTuned.method q (budget q 0), ?_, fun _ _ => trivial⟩
  intro q hv f O hO
  exact LongTails.Proofs.CovarianceAcceleratedSpecification.successful_execution q hv f O hO

end LongTails.Theorems.CovarianceAcceleratedHighProbability
