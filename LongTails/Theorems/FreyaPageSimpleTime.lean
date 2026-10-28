import LongTails.Template
import LongTails.Setups.FreyaPageSimpleTime
import LongTails.Proofs.FreyaTunedComplexity

open OracleTemplate

namespace LongTails.Theorems.FreyaPageSimpleTime

noncomputable def budget : (let S := LongTails.Setups.FreyaPageSimpleTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * p.m * (⌈4 * p.Δ * max p.Lminus p.Lpm / p.ε⌉₊ + 2)

attribute [local simp] budget

theorem result : Convergence LongTails.Setups.FreyaPageSimpleTime.spec budget := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      refine ⟨LongTails.Algorithms.FreyaTuning.simple, ?_, ?_⟩
      · intro p hp f O hO
        exact LongTails.Proofs.FreyaTunedComplexity.simple_execution_accuracy p hp f O hO
      · intro p _
        rfl


end LongTails.Theorems.FreyaPageSimpleTime
