import LongTails.Setups.HeavyTailedHighProbabilityStationarity
import LongTails.Proofs.HeavyTailedHighProbabilityUpper

namespace LongTails.Theorems.HeavyTailedHighProbabilityStationarityUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HeavyTailedHighProbabilityStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let s := (2 ^ 45 * q.σ / q.ε) ^ (q.p / (q.p - 1))
  let ℓ := Real.log (16 / q.δ)
  ⌈2 ^ 76 * ((1 + s) * (q.L * q.Δ / q.ε ^ 2 + ℓ * Real.log (2 + ℓ) ^ (2 + 2 / q.p)) + Real.sqrt (q.L * q.Δ) * ℓ / q.ε)⌉₊

theorem result : Convergence LongTails.Setups.HeavyTailedHighProbabilityStationarity.spec budget :=
  LongTails.Proofs.HeavyTailedHighProbabilityUpper.convergence

end LongTails.Theorems.HeavyTailedHighProbabilityStationarityUpperBound
