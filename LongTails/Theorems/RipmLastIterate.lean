import LongTails.Setups.RipmLastIterate
import LongTails.Proofs.RipmAccuracy

namespace LongTails.Theorems.RipmLastIterate

noncomputable def budget : (let S := LongTails.Setups.RipmLastIterate.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(64 * (1 + 10 * (p.L * p.D2 + p.Delta + (p.S + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L) / p.epsilon) * (1 + Real.log (1 + 10 * (p.L * p.D2 + p.Delta + (p.S + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L) / p.epsilon))) ^ 2⌉₊ + 1

theorem result : OracleTemplate.Convergence LongTails.Setups.RipmLastIterate.spec budget := by
  refine ⟨LongTails.Algorithms.RipmOutput.method, ?_, ?_⟩
  · intro p hp I O hO
    exact LongTails.Proofs.RipmAccuracy.target_execution_accuracy p hp I O hO
  · intro p hp
    rfl


end LongTails.Theorems.RipmLastIterate
