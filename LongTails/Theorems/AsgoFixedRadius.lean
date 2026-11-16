import LongTails.Setups.AsgoFixedRadius
import LongTails.Proofs.AsgoFixedRadiusRate

namespace OracleTemplate.AsgoFixedRadius

noncomputable def budget : (let S := LongTails.Setups.AsgoFixedRadius.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.M * (⌈8 * p.R ^ 2 * p.ell / p.delta + 4 * p.k * p.F ^ 2 / (p.R * p.delta) + 32 * p.R ^ 2 * p.v ^ 2 / ((p.M : ℝ) * p.delta ^ 2)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.AsgoFixedRadius.spec budget := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    refine ⟨LongTails.Setups.AsgoFixedRadius.Core.method, ?_, ?_⟩
    · intro p hp I O hO
      exact execution_accuracy p hp I O hO
    · intro p _
      rfl
  )

end OracleTemplate.AsgoFixedRadius
