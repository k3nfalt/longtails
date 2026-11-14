import LongTails.Setups.RipmGeneral
import LongTails.Proofs.RipmAccuracy

namespace LongTails.Theorems.RipmGeneral

noncomputable def budget : (let S := LongTails.Setups.RipmGeneral.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(64 * (1 + 3 * (p.C * p.L * p.D2 + 2 * p.Delta + (4 * p.S / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L) / p.epsilon) * (1 + Real.log (1 + 3 * (p.C * p.L * p.D2 + 2 * p.Delta + (4 * p.S / (p.C - 2) + 16 * (p.m : ℝ) ^ 2 * p.Lg ^ 2 / p.C) / p.L) / p.epsilon))) ^ 2⌉₊ + 1

theorem result : OracleTemplate.Convergence LongTails.Setups.RipmGeneral.spec budget := by
  refine ⟨LongTails.Algorithms.RipmOutput.method, ?_, ?_⟩
  · intro p hp I O hO
    exact LongTails.Proofs.RipmAccuracy.general_execution_accuracy p hp I O hO
  · intro p hp
    rfl


end LongTails.Theorems.RipmGeneral
