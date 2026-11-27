import LongTails.Setups.SlidingStochasticComposite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory

namespace LongTails.Setups.HighDimensionalSlidingStochasticComposite

open OracleTemplate

structure Params where
  d : ℕ
  ℓ : ℝ
  L : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  c : Fin 2
  K : ℕ

noncomputable abbrev toGeneral (q : Params) : LongTails.Setups.SlidingStochasticComposite.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := Bool
  ℓ := q.ℓ
  L := q.L
  σ := q.σ
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance q := LongTails.Setups.SlidingStochasticComposite.Instance (toGeneral q)
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := 0 < q.ℓ ∧ q.ℓ ≤ q.L ∧ 0 ≤ q.σ ∧ 0 < q.ε ∧ 2 ^ 62 * q.ε ^ 2 ≤ q.ℓ * q.Δ ∧
    2 ^ 200 * (1 + q.K + q.ℓ * q.Δ / q.ε ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ))) *
      (1 + q.ℓ * q.Δ / q.ε ^ 2) ^ 3 * (1 + Real.sqrt (q.L / q.ℓ)) ^ 9 ≤ (q.d : ℝ)
  admissible q I O := LongTails.Setups.SlidingStochasticComposite.spec.admissible (toGeneral q) I O
  successful q I output P :=
    LongTails.Setups.SlidingStochasticComposite.spec.successful (toGeneral q) I output P

end LongTails.Setups.HighDimensionalSlidingStochasticComposite
