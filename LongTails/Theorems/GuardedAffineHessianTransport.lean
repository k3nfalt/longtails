import LongTails.Setups.GeneralizedAffineHessianVector
import LongTails.Algorithms.ValidatedHessianTransport
import LongTails.Proofs.ValidatedHessianAccuracy
import LongTails.Proofs.ValidatedHessianTuning

namespace OracleTemplate.GuardedAffineHessianTransport

open LongTails.Setups.GeneralizedAffineHessianVector

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ (100 * (p.p / (p.p - 1)) + 100) * (1 + (p.p / (p.p - 1))) * (1 + Real.log (2 + (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε) / p.ε + (p.Δ * (p.L0 + p.σh + (p.L1 + p.αh) * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε) + p.ε / (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε)) / p.ε ^ 2) + (1 + (p.σg + p.αg * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε)) / p.ε))) ^ ((p.p / (p.p - 1)) + 1) * ((1 + (p.σg + p.αg * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε)) / p.ε) ^ (p.p / (p.p - 1)) + (p.Δ * (p.L0 + p.σh + (p.L1 + p.αh) * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε) + p.ε / (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε)) / p.ε ^ 2) * (1 + (p.σg + p.αg * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε)) / p.ε) ^ ((p.p / (p.p - 1)) / p.q) * (1 + p.σg / (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε) + p.αg) ^ (p.p / (p.p - 1)))⌉₊

theorem result : Convergence LongTails.Setups.GeneralizedAffineHessianVector.spec budget := by
  refine ⟨LongTails.Algorithms.ValidatedHessianTransport.tunedAlgorithm, ?_, ?_⟩
  · intro p hp f O hO
    exact LongTails.Proofs.ValidatedHessianAccuracy.specification_successful p hp f O hO
      ⌈LongTails.Proofs.ValidatedHessianTuning.envelope p⌉₊
      (LongTails.Proofs.ValidatedHessianTuning.calls_le_budget p hp)
  · intro p hp
    trivial

end OracleTemplate.GuardedAffineHessianTransport
