import LongTails.Setups.StochasticThirdOrderSmoothNonconvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory

namespace LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  L₁ : ℝ
  L₂ : ℝ
  L₃ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) :
    LongTails.Setups.StochasticThirdOrderSmoothNonconvex.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L₁ := q.L₁
  L₂ := q.L₂
  L₃ := q.L₃
  σ := q.σ
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
  valid q := 0 < q.L₁ ∧ 0 < q.L₂ ∧ 0 < q.L₃ ∧ 0 ≤ q.σ ∧ 0 < q.ε ∧
    2 ^ 70 * q.ε ≤ q.Δ * min (q.L₁ / q.ε) (min (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ))) ∧
    2 ^ 140 * (1 + q.Δ * min (q.L₁ / q.ε) (min (Real.sqrt (q.L₂ / q.ε)) ((q.L₃ / q.ε) ^ (1 / 3 : ℝ))) * (1 + q.σ ^ 2 / q.ε ^ 2) / q.ε) ^ 4 ≤ (q.d : ℝ)
  admissible q f O :=
    LongTails.Setups.StochasticThirdOrderSmoothNonconvex.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.StochasticThirdOrderSmoothNonconvex.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex
