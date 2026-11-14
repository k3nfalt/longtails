import LongTails.Setups.HighDimensionalConstrainedQuasar
import LongTails.Proofs.HighDimensionalQuasarInclusion
import LongTails.Theorems.StochasticConstrainedQuasarHighProbability

namespace LongTails.Theorems.HighDimensionalConstrainedQuasarUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalConstrainedQuasar.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(2 : ℝ) ^ 96 * (2 + ⌈8 * Real.log (8 / q.δ)⌉₊) * (1 + Nat.clog 2 ⌈2 + q.L * q.D ^ 2 / (q.γ ^ 2 * q.ε)⌉₊) ^ 2 * (1 + Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ + q.σ ^ 2 * q.D ^ 2 / (q.γ ^ 2 * q.ε ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.HighDimensionalConstrainedQuasar.spec budget := by
  obtain ⟨make, correct, _⟩ := OracleTemplate.StochasticQuasar.result
  refine ⟨fun p => make p.toStochastic, ?_, fun _ _ => trivial⟩
  intro p hp I O h
  exact correct p.toStochastic (HighDimensionalQuasar.inclusion.valid p hp) I O h

end LongTails.Theorems.HighDimensionalConstrainedQuasarUpperBound
