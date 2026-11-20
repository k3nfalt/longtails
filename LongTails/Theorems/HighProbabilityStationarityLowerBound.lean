import LongTails.Setups.HighDimensionalHighProbabilityStationarity
import LongTails.Proofs.HighProbabilityLowerAssembly
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.HighProbabilityStationarityLowerBound

open OracleTemplate MeasureTheory

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalHighProbabilityStationarity.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊(q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2) + q.σ ^ 2 * Real.log (1 / (4 * q.δ))) / (2 ^ 54 * q.ε ^ 2)⌋₊

theorem result :
    NonConvergence LongTails.Setups.HighDimensionalHighProbabilityStationarity.spec budget :=
  LongTails.Proofs.HighProbabilityLowerAssembly.nonConvergence

end LongTails.Theorems.HighProbabilityStationarityLowerBound
