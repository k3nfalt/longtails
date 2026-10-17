import LongTails.Setups.PLHessianLipschitzKurtosis
import LongTails.Proofs.PLHessianConvergence

namespace OracleTemplate.PLHessian

open LongTails.Setups.PLHessianLipschitzKurtosis

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈32 * (16 * q.L + 14 * q.L * Real.sqrt (Real.sqrt (q.L / q.μ)) + 28311552 * q.K * Real.sqrt (q.L / q.μ) * q.L * q.σ ^ 2 * q.ρ ^ 2 / q.μ ^ 4 + 64 * q.σ ^ 2 / q.ε) / q.μ * (Real.log (1 + 6 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε) + 1) + 512 * q.σ ^ 2 / (q.μ * q.ε)⌉₊ + 1

theorem result : Convergence LongTails.Setups.PLHessianLipschitzKurtosis.spec budget :=
  convergence

end OracleTemplate.PLHessian
