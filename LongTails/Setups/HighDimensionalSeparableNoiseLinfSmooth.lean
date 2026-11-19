import LongTails.Setups.SeparableNoiseLinfSmooth

open MeasureTheory

namespace LongTails.Setups.HighDimensionalSeparableNoiseLinfSmooth

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  S : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.SeparableNoiseLinfSmooth.Params where
  d := q.d
  Ω := ℝ
  L := q.L
  S := q.S
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
  valid q := 0 < q.L ∧ 0 ≤ q.S ∧ 0 < q.ε ∧ 2 ^ 30 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    2 ^ 168 * (1 + q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) / q.ε ^ 2) ^ 16 ≤ (q.d : ℝ)
  admissible q f O :=
    LongTails.Setups.SeparableNoiseLinfSmooth.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.SeparableNoiseLinfSmooth.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalSeparableNoiseLinfSmooth
