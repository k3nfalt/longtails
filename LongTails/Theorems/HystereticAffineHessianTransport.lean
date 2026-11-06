import LongTails.Setups.GeneralizedAffineHessianVector
import LongTails.Algorithms.HystereticHessianTransport
import LongTails.Proofs.HystereticHessianAccuracy
import LongTails.Proofs.HystereticHessianBudget

namespace OracleTemplate.HystereticAffineHessianTransport

open LongTails.Setups.GeneralizedAffineHessianVector

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ (32 * (p.p / (p.p - 1)) + 16 * p.q / (p.q - 1) + 64) * (p.p / (p.p - 1) + 1) * (1 + Real.log (2 + (1 + p.σg / p.ε + p.αg) + p.Δ * (p.L0 + p.σh + (p.L1 + p.αh) * (p.ε + p.σg / (1 + p.αg))) / p.ε ^ 2 + (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε + p.σg) / p.ε)) * ((1 + p.σg / p.ε + p.αg) ^ (p.p / (p.p - 1)) + p.Δ * (p.L0 + p.σh + (p.L1 + p.αh) * (p.ε + p.σg / (1 + p.αg))) / p.ε ^ 2 * ((1 + p.σg / p.ε + p.αg) ^ ((p.p / (p.p - 1)) / p.q) + (1 + p.αg) ^ 2 * (1 + p.σg / p.ε + p.αg) ^ (p.p / (p.p - 1) - 2)))⌉₊

theorem result : Convergence LongTails.Setups.GeneralizedAffineHessianVector.spec budget := by
  refine ⟨LongTails.Algorithms.HystereticHessianTransport.tunedAlgorithm, ?_, ?_⟩
  · intro p hp f O hO
    exact LongTails.Proofs.HystereticHessianAccuracy.specification_successful p hp f O hO
      ⌈LongTails.Proofs.HystereticHessianBudget.envelope p⌉₊
      (LongTails.Proofs.HystereticHessianBudget.calls_le_budget p hp)
  · intro p hp
    trivial

end OracleTemplate.HystereticAffineHessianTransport
