import LongTails.Setups.StochasticWeakMinty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HighDimensionalStochasticWeakMinty

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  ρ : ℝ
  σ : ℝ
  R : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.StochasticWeakMinty.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  ρ := q.ρ
  σ := q.σ
  R := q.R
  ε := q.ε
  x0 := q.x0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → EuclideanSpace ℝ (Fin q.d)
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := LongTails.Setups.StochasticWeakMinty.spec.valid (toGeneral q) ∧
    2 ^ 10 * q.ε ≤ q.L * q.R ∧
    q.L ^ 6 * q.R ^ 6 * (q.ε ^ 2 + q.σ ^ 2) ≤ q.ε ^ 8 * q.d
  admissible q F O := LongTails.Setups.StochasticWeakMinty.spec.admissible (toGeneral q) F O
  successful q F output P :=
    LongTails.Setups.StochasticWeakMinty.spec.successful (toGeneral q) F output P

end LongTails.Setups.HighDimensionalStochasticWeakMinty
