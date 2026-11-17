import LongTails.Setups.PointwiseHessianStationarity
import LongTails.Proofs.RelativeHessianHardness

namespace LongTails.Theorems.PointwiseHessianStationarityLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.PointwiseHessianStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (2 ^ 39 * p.ε * Real.sqrt p.ε)⌋₊

theorem result : NonConvergence LongTails.Setups.PointwiseHessianStationarity.spec budget := by
  intro p hp A _ b hb
  apply LongTails.Proofs.RelativeHessianHardness.hard p hp A b
  convert hb 0 using 1
  unfold budget LongTails.Proofs.RelativeHessianTuning.limit LongTails.Proofs.RelativeHessianTuning.scale
  congr 1
  ring

end LongTails.Theorems.PointwiseHessianStationarityLowerBound
