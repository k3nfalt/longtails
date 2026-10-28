import LongTails.Template
import outputs.Setups.FreyaPageSimpleTime
import outputs.Proofs.FreyaTunedComplexity

open OracleTemplate

namespace outputs.Theorems.FreyaPageSimpleTime

noncomputable def budget : (let S := outputs.Setups.FreyaPageSimpleTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * p.m * (⌈4 * p.Δ * max p.Lminus p.Lpm / p.ε⌉₊ + 2)

attribute [local simp] budget

theorem result : Convergence outputs.Setups.FreyaPageSimpleTime.spec budget := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      refine ⟨outputs.Algorithms.FreyaTuning.simple, ?_, ?_⟩
      · intro p hp f O hO
        exact outputs.Proofs.FreyaTunedComplexity.simple_execution_accuracy p hp f O hO
      · intro p _
        rfl


end outputs.Theorems.FreyaPageSimpleTime
