import LongTails.Template
import outputs.Setups.FreyaPageOptimizedTime
import outputs.Proofs.FreyaTunedComplexity

open OracleTemplate

namespace outputs.Theorems.FreyaPageOptimizedTime

noncomputable def budget : (let S := outputs.Setups.FreyaPageOptimizedTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * p.m * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt p.m) / p.ε⌉₊ + 2)

attribute [local simp] budget

theorem result : Convergence outputs.Setups.FreyaPageOptimizedTime.spec budget := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      refine ⟨outputs.Algorithms.FreyaTuning.optimized, ?_, ?_⟩
      · intro p hp f O hO
        exact outputs.Proofs.FreyaTunedComplexity.optimized_execution_accuracy p hp f O hO
      · intro p _
        rfl


end outputs.Theorems.FreyaPageOptimizedTime
