import LongTails.Setups.BiasedNoiseNonconvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalBiasedNoiseNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  m : ℝ
  M : ℝ
  σ : ℝ
  ζ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin (d + 1))

noncomputable def toGeneral (q : Params) : LongTails.Setups.BiasedNoiseNonconvex.Params where
  E := EuclideanSpace ℝ (Fin (q.d + 1))
  Ω := ℝ
  L := q.L
  m := q.m
  M := q.M
  σ := q.σ
  ζ := q.ζ
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin (q.d + 1)) → ℝ
  Query q := EuclideanSpace ℝ (Fin (q.d + 1))
  Reply q := EuclideanSpace ℝ (Fin (q.d + 1))
  Output q := EuclideanSpace ℝ (Fin (q.d + 1))
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.m ∧ q.m < 1 ∧ 0 ≤ q.M ∧ 0 ≤ q.σ ∧ 0 ≤ q.ζ ∧ 0 < q.ε ∧
    16 * q.ζ ^ 2 ≤ (1 - q.m) * q.ε ^ 2 ∧ 2 ^ 28 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    2 ^ 40 * (1 + q.L * q.Δ * (1 + q.M + q.σ ^ 2 / ((1 - q.m) * q.ε ^ 2)) /
      ((1 - q.m) * q.ε ^ 2)) ^ 4 ≤ (q.d : ℝ)
  admissible q f O :=
    LongTails.Setups.BiasedNoiseNonconvex.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.BiasedNoiseNonconvex.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalBiasedNoiseNonconvex
