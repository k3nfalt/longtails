import LongTails.Setups.PointwiseHessianStationarity
import LongTails.Proofs.HessianModelFlowExecution

namespace LongTails.Theorems.PointwiseHessianModelFlow

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.PointwiseHessianStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let S := p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)
  ⌊32 * S / 3⌋₊ + 1

theorem result : Convergence LongTails.Setups.PointwiseHessianStationarity.spec budget := by
  refine ⟨LongTails.Algorithms.PointwiseHessianModelFlow.algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hf
  exact LongTails.Proofs.HessianModelFlowExecution.success hp.1 f O hf (budget p 0)
    (LongTails.Proofs.HessianModelFlowExecution.budget_large hp.1)

end LongTails.Theorems.PointwiseHessianModelFlow
