import LongTails.Template
import outputs.Setups.FreyaPageTime
import outputs.Proofs.FreyaFreeTime

open OracleTemplate

namespace outputs.Theorems.FreyaPageTime

noncomputable def budget : (let S := outputs.Setups.FreyaPageTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * p.m + (p.n * p.m + p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1)

attribute [local simp] budget

theorem result : Convergence outputs.Setups.FreyaPageTime.spec budget := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      refine ⟨outputs.Algorithms.FreyaTuning.freeTime, ?_, ?_⟩
      · intro p hp f O hO
        exact outputs.Proofs.FreyaFreeTime.free_time_execution_accuracy p hp f O hO
      · intro p _
        rfl


end outputs.Theorems.FreyaPageTime
