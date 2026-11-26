import LongTails.Setups.VarianceOnlySecondOrder
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory

namespace LongTails.Setups.HighDimensionalVarianceOnlySecondOrder

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  ρ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ

noncomputable def toGeneral (q : Params) : LongTails.Setups.VarianceOnlySecondOrder.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  ρ := q.ρ
  σ := q.σ
  Δ := q.Δ
  ε := q.ε
  δ := q.δ
  x0 := 0

def measurablePolicy {q : Params}
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) : Prop :=
  ∃ space : MeasurableSpace A.State,
    letI := space
    Measurable A.initial ∧ Measurable A.query ∧ Measurable A.update.uncurry ∧ Measurable A.output

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q :=
    let D := Real.sqrt q.ρ * q.Δ / (q.ε * Real.sqrt q.ε)
    LongTails.Setups.VarianceOnlySecondOrder.spec.valid (toGeneral q) ∧ q.δ ≤ 1 / 2 ∧
      2 ^ 130 * Real.sqrt (q.ρ * q.ε) ≤ q.L ∧ 2 ^ 200 * q.ε ≤ q.σ ∧ 2 ^ 390 ≤ D ∧
      D ^ 2 * Real.log (q.d * q.σ * D / q.ε) ≤ 2 ^ 480 * q.d
  allowedAlgorithm _ A := measurablePolicy A
  admissible q f O := LongTails.Setups.VarianceOnlySecondOrder.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.VarianceOnlySecondOrder.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalVarianceOnlySecondOrder
