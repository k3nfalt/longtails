import LongTails.Setups.StochasticEllSmoothNonconvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  ℓ : ℝ → ℝ
  ρ : ℝ
  p : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.StochasticEllSmoothNonconvex.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  ℓ := q.ℓ
  ρ := q.ρ
  p := q.p
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
  valid q := LongTails.Setups.StochasticEllSmoothNonconvex.spec.valid (toGeneral q) ∧ 0 < q.ℓ 0 ∧
    2 ^ 28 * q.ε ^ 2 ≤ (2 - q.ρ) * q.Δ * q.ℓ q.ε ∧
    2 ^ 56 * ((2 - q.ρ) * (q.Δ * q.ℓ q.ε / q.ε ^ 2) *
        max 1 ((q.σ / (2 ^ 13 * q.ε)) ^ (q.p / (q.p - 1))) / 2 ^ 27 + 1) ^ 6 *
      (q.ℓ q.ε / q.ℓ 0) ^ 4 ≤ q.d
  admissible q f O :=
    LongTails.Setups.StochasticEllSmoothNonconvex.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.StochasticEllSmoothNonconvex.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex
