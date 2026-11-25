import LongTails.Setups.StochasticNonconvexPL
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalStochasticNonconvexPL

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  μ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  y0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.StochasticNonconvexPL.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  F := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  μ := q.μ
  σ := q.σ
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0
  y0 := q.y0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := LongTails.Setups.StochasticNonconvexPL.spec.valid (toGeneral q) ∧
    2 ^ 47 * q.μ ≤ q.L ∧
    2 ^ 47 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    2 ^ 99 * (q.L ^ 2 * q.Δ / (q.μ * q.ε ^ 2) * (1 + q.L * q.σ ^ 2 / (q.μ * q.ε ^ 2)) + 1) *
      (q.L * q.Δ / q.ε ^ 2) ^ 2 * (q.L / q.μ) ^ 3 ≤ q.d
  admissible q f O := LongTails.Setups.StochasticNonconvexPL.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.StochasticNonconvexPL.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalStochasticNonconvexPL
