import LongTails.Template
import outputs.Setups.FreyaPageUniform
import outputs.Proofs.FreyaSerialAnalysis

open OracleTemplate

namespace outputs.Theorems.FreyaPageUniform

noncomputable def budget : (let S := outputs.Setups.FreyaPageUniform.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.m + (p.m + 2 * p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1)

attribute [local simp] budget

theorem result : Convergence outputs.Setups.FreyaPageUniform.spec budget := by
  refine ⟨outputs.Algorithms.FreyaTuning.serial, ?_, ?_⟩
  · intro p hp f O hO
    exact outputs.Proofs.FreyaSerialAnalysis.serial_execution_accuracy p hp f O hO
  · intro p _
    rfl


end outputs.Theorems.FreyaPageUniform
