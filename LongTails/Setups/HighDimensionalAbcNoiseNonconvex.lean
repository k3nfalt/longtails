import LongTails.Setups.AbcNoiseNonconvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalAbcNoiseNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.AbcNoiseNonconvex.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  A := q.A
  B := q.B
  C := q.C
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.A ∧ 0 ≤ q.B ∧ 0 ≤ q.C ∧ 0 < q.ε ∧
    2 ^ 26 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    2 ^ 40 * (1 + q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2) ^ 4 ≤
      (q.d : ℝ)
  admissible q f O := LongTails.Setups.AbcNoiseNonconvex.spec.admissible (toGeneral q) f O
  successful q f output P := LongTails.Setups.AbcNoiseNonconvex.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalAbcNoiseNonconvex
