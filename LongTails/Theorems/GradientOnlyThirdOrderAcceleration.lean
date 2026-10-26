import LongTails.Setups.GradientOnlyThirdOrderNonconvex
import LongTails.Proofs.GradientOnlyExecution

namespace OracleTemplate.GradientOnlyThirdOrderAcceleration

open LongTails.Setups.GradientOnlyThirdOrderNonconvex
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Proofs.GradientOnlyExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌊2048 * p.Δ * p.L₃ ^ (1 / 3 : ℝ) / p.ε ^ (4 / 3 : ℝ)⌋₊ + 1) * (97 * ⌈Real.sqrt (p.L₁ / (p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)) + 4) * Real.log (1 + 200 * (p.L₁ + 4 * p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)) * p.Δ / p.ε ^ 2)⌉₊ + 290)

theorem result : Convergence LongTails.Setups.GradientOnlyThirdOrderNonconvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  exact Filter.Eventually.of_forall fun ω =>
    run_accuracy p hp f O ho _ (epochLength_tuning p).le ω.1 ω.2

end OracleTemplate.GradientOnlyThirdOrderAcceleration
