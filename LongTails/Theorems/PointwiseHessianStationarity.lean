import LongTails.Setups.PointwiseHessianStationarity
import LongTails.Algorithms.JointHessianStationarity
import LongTails.Proofs.JointHessianStationarity
import LongTails.Proofs.JointHessianBudget

namespace LongTails.Theorems.PointwiseHessianStationarity

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.PointwiseHessianStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈100000 * p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)⌉₊ + 2 * ⌈Real.log (1 + p.L₁ * p.G / (p.L₀ + p.L₁ * p.ε)) / Real.log (4 / 3)⌉₊ + 200

theorem result : Convergence LongTails.Setups.PointwiseHessianStationarity.spec budget := by
  refine ⟨LongTails.Algorithms.JointHessianStationarity.algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hf
  exact LongTails.Proofs.JointHessianStationarity.success hp.1 f O hf (budget p 0)
    (LongTails.Proofs.JointHessianBudget.sufficient hp.1)

end LongTails.Theorems.PointwiseHessianStationarity
