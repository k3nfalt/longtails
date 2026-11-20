import LongTails.Setups.HighProbabilityStationarity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalHighProbabilityStationarity

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.HighProbabilityStationarity.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  σ := q.σ
  Δ := q.Δ
  ε := q.ε
  δ := q.δ
  x0 := q.x0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.σ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ ≤ 1 / 4 ∧
    2 ^ 54 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    2 ^ 40 * (1 + q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2) / q.ε ^ 2) ^ 4 ≤ (q.d : ℝ)
  admissible q f O :=
    LongTails.Setups.HighProbabilityStationarity.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.HighProbabilityStationarity.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalHighProbabilityStationarity
