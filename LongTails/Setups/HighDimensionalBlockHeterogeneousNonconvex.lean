import LongTails.Setups.BlockHeterogeneousNonconvex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  B : ℕ
  blk : Fin d → Fin B
  L : Fin B → ℝ
  σ : Fin B → ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def toGeneral (q : Params) : LongTails.Setups.BlockHeterogeneousNonconvex.Params where
  d := q.d
  B := q.B
  blk := q.blk
  Ω := ℝ
  L := q.L
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
  valid q := 0 < q.B ∧ (∀ j, 0 < q.L j) ∧ (∀ j, 0 ≤ q.σ j) ∧ 0 < q.ε ∧
    (∀ j, 2 ^ 57 * q.ε ^ 2 ≤ q.L j * q.Δ) ∧
    ∀ j, 2 ^ 40 * (1 + q.B * (∑ i, q.L i) * q.Δ / q.ε ^ 2 +
      (∑ i, (q.L i * q.σ i ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4) ^ 4 ≤
        (Fintype.card {i // q.blk i = j} : ℝ)
  admissible q f O :=
    LongTails.Setups.BlockHeterogeneousNonconvex.spec.admissible (toGeneral q) f O
  successful q f output P :=
    LongTails.Setups.BlockHeterogeneousNonconvex.spec.successful (toGeneral q) f output P

end LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex
