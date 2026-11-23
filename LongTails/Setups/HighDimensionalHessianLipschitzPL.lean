import LongTails.Setups.HessianLipschitzPL
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.HighDimensionalHessianLipschitzPL

open OracleTemplate

structure Params where
  d : ℕ
  H : ℝ
  μ : ℝ
  Δ : ℝ
  ε : ℝ

noncomputable def toGeneral (q : Params) : LongTails.Setups.HessianLipschitzPL.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  H := q.H
  x0 := 0
  μ := q.μ
  Δ := q.Δ
  ε := q.ε

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := ℝ × EuclideanSpace ℝ (Fin q.d) ×
    (EuclideanSpace ℝ (Fin q.d) →L[ℝ] EuclideanSpace ℝ (Fin q.d))
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := 0 < q.H ∧ 0 < q.μ ∧ 0 < q.ε ∧ 32 * q.ε ≤ q.Δ ∧
    2 ^ 160 ≤ q.H ^ 2 * q.Δ / q.μ ^ 3 ∧ q.H ^ 2 * q.Δ / q.μ ^ 3 ≤ q.d
  admissible q f O := LongTails.Setups.HessianLipschitzPL.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.HessianLipschitzPL.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalHessianLipschitzPL
