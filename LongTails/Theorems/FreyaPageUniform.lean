import LongTails.Template
import LongTails.Setups.FreyaPageUniform
import LongTails.Proofs.FreyaSerialAnalysis

open OracleTemplate

namespace LongTails.Theorems.FreyaPageUniform

noncomputable def budget : (let S := LongTails.Setups.FreyaPageUniform.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.m + (p.m + 2 * p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1)

attribute [local simp] budget

theorem result : Convergence LongTails.Setups.FreyaPageUniform.spec budget := by
  refine ⟨LongTails.Algorithms.FreyaTuning.serial, ?_, ?_⟩
  · intro p hp f O hO
    exact LongTails.Proofs.FreyaSerialAnalysis.serial_execution_accuracy p hp f O hO
  · intro p _
    rfl


end LongTails.Theorems.FreyaPageUniform
