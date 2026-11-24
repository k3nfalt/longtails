import LongTails.Setups.MeanSquaredSmoothPL

namespace LongTails.Setups.HighDimensionalMeanSquaredSmoothPL

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  Lbar : ℝ
  μ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def Params.toGeneral (q : Params) : MeanSquaredSmoothPL.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := ℝ
  L := q.L
  Lbar := q.Lbar
  μ := q.μ
  σ := q.σ
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := MeanSquaredSmoothPL.spec.valid q.toGeneral ∧ 2 ^ 73 * q.μ ≤ q.L ∧
    64 * q.ε ≤ q.Δ ∧ (q.L / q.μ) ^ 4 * (1 + q.σ ^ 2 / (q.μ * q.ε)) ≤ q.d
  admissible q f O := MeanSquaredSmoothPL.spec.admissible q.toGeneral f O
  successful q f output P := MeanSquaredSmoothPL.spec.successful q.toGeneral f output P

end LongTails.Setups.HighDimensionalMeanSquaredSmoothPL
