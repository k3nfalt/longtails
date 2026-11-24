import LongTails.Setups.HeavyTailedNcsc
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalHeavyTailedNcsc

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  μ : ℝ
  p : ℝ
  σ : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ
  δ : ℝ

noncomputable def toGeneral (q : Params) : LongTails.Setups.HeavyTailedNcsc.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  F := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  μ := q.μ
  p := q.p
  σ := q.σ
  Δ := q.Δ
  G := q.G
  ε := q.ε
  δ := q.δ
  x0 := 0
  y0 := 0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := LongTails.Setups.HeavyTailedNcsc.spec.valid (toGeneral q) ∧ q.δ ≤ 1 / 4 ∧
    8 * q.μ ≤ q.L ∧ 2 ^ 32 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    4176 * q.ε ≤ q.G * Real.sqrt (q.L / q.μ) ∧
    2 ^ 40 * (1 + q.L * q.Δ / q.ε ^ 2 *
      (1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ (q.p / (q.p - 1)))) ^ 4 ≤ (q.d : ℝ)
  admissible q f O := LongTails.Setups.HeavyTailedNcsc.spec.admissible (toGeneral q) f O
  successful q f output P := LongTails.Setups.HeavyTailedNcsc.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalHeavyTailedNcsc
