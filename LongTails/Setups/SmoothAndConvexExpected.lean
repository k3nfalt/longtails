import LongTails.Setups.SmoothAndConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Setups.SmoothAndConvexExpected

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  L : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  R : ℝ
  ε : ℝ

noncomputable abbrev Params.toSmoothAndConvex (q : Params) : SmoothAndConvex.Params :=
  { E := EuclideanSpace ℝ (Fin q.d), L := q.L, x0 := q.x0, R := q.R, ε := q.ε }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := id
  valid q := 0 < q.L ∧ 0 < q.R ∧ 0 < q.ε ∧ 262144 * q.ε ≤ q.L * q.R ^ 2 ∧
    65536 * (⌊Real.sqrt (q.L * q.R ^ 2 / q.ε) / 512⌋₊ + 1) ^ 5 ≤ q.d
  admissible q := SmoothAndConvex.spec.admissible q.toSmoothAndConvex
  successful q f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.SmoothAndConvexExpected
