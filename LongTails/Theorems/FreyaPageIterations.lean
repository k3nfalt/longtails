import LongTails.Template
import LongTails.Setups.FreyaPageIterations
import LongTails.Proofs.FreyaIterations

open OracleTemplate

namespace LongTails.Theorems.FreyaPageIterations

noncomputable def budget : (let S := LongTails.Setups.FreyaPageIterations.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * p.m + (p.n * p.m + p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1)

attribute [local simp] budget

theorem result : Convergence LongTails.Setups.FreyaPageIterations.spec budget := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      refine ⟨LongTails.Algorithms.FreyaTuning.iterations, ?_, ?_⟩
      · intro p hp f O hO
        exact LongTails.Proofs.FreyaIterations.iterations_execution_accuracy p hp f O hO
      · intro p _
        rfl


end LongTails.Theorems.FreyaPageIterations
