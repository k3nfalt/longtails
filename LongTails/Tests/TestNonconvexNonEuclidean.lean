import LongTails.Setups.SmoothNonconvexNonEuclidean
import Mathlib.Analysis.Calculus.FDeriv.Const

namespace OracleTemplate.NonconvexDerivativeTests

open LongTails.Setups.SmoothNonconvexNonEuclidean

abbrev Plane := Fin 2 → ℝ

theorem maximum_norm : ‖(1 : Plane)‖ = 1 := norm_one

theorem constant_objective_admissible :
    spec.admissible { E := Plane, L := 1, Δ := 0, ε := 1, x0 := 0 } (fun _ => 0)
      { answer := fun _ (_, _) _ => 0 } := by
  refine ⟨fun _ _ x => hasFDerivAt_const (0 : ℝ) x,
    fun x => ?_, ?_, ⟨0, fun _ => le_rfl, by simp⟩⟩
  · simpa using hasFDerivAt_const (0 : ℝ) x
  · intro x y
    simp

end OracleTemplate.NonconvexDerivativeTests
