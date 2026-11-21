import LongTails.Setups.HighProbabilityStationarity
import LongTails.Proofs.HighProbabilityUpperAssembly

namespace LongTails.Theorems.HighProbabilityStationarityUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighProbabilityStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 71 * ((1 + q.σ ^ 2 / q.ε ^ 2) * (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ 3) + Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊

theorem result : Convergence LongTails.Setups.HighProbabilityStationarity.spec budget :=
  LongTails.Proofs.HighProbabilityUpperAssembly.convergence

end LongTails.Theorems.HighProbabilityStationarityUpperBound
