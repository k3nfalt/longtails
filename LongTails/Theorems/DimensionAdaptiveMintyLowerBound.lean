import LongTails.TemplateLowerBound
import LongTails.Setups.FiniteDimensionalWeakMinty
import LongTails.Proofs.MintyDimensionLowerBound

namespace LongTails.Theorems.DimensionAdaptiveMintyLowerBound

open OracleTemplate LongTails.Setups.FiniteDimensionalWeakMinty

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  ⌊(p.d / (2 ^ 22 : ℝ)) * Real.log (1 + (p.L * p.R) ^ 2 / (p.d * p.ε ^ 2))⌋₊

theorem result : NonConvergence LongTails.Setups.FiniteDimensionalWeakMinty.spec budget := by
  intro p hp A _ b hb
  have he : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [he]
  have h := hb 0
  simp only [budget, LongTails.Proofs.MintyDimensionBudget.scaled_ratio, div_mul_eq_mul_div] at h
  obtain ⟨F, ha, hf⟩ := LongTails.Proofs.MintyDimensionLowerBound.failure p hp A (b 0) h
  exact ⟨F, _, ha, hf⟩

end LongTails.Theorems.DimensionAdaptiveMintyLowerBound
