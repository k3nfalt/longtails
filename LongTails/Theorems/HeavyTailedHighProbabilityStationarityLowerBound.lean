import LongTails.Setups.HighDimensionalHeavyTailedHighProbabilityStationarity
import LongTails.Proofs.HeavyTailedHighProbabilityLower
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.HeavyTailedHighProbabilityStationarityLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalHeavyTailedHighProbabilityStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let s := (q.σ / (2 ^ 12 * q.ε)) ^ (q.p / (q.p - 1))
  ⌊((1 + s) * q.L * q.Δ / q.ε ^ 2 + s * Real.log (1 / (4 * q.δ))) / 2 ^ 55⌋₊

theorem result :
    NonConvergence LongTails.Setups.HighDimensionalHeavyTailedHighProbabilityStationarity.spec budget :=
  LongTails.Proofs.HeavyTailedHighProbabilityLower.nonConvergence

end LongTails.Theorems.HeavyTailedHighProbabilityStationarityLowerBound
