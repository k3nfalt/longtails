import LongTails.Setups.HolderNoiseNonconvex

namespace LongTails.Setups.HolderNoiseNonconvexLower

open OracleTemplate

structure LowerParams where
  d : ℕ
  L : ℝ
  M : ℝ
  ν : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

noncomputable def LowerParams.toParams (q : LowerParams) : HolderNoiseNonconvex.Params where
  E := EuclideanSpace ℝ (Fin q.d)
  Ω := Bool
  L := q.L
  M := q.M
  ν := q.ν
  σ := q.σ
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

abbrev spec : Setup where
  Params := LowerParams
  Public := LowerParams
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := HolderNoiseNonconvex.spec.valid q.toParams ∧ 64 * q.ε ^ 2 ≤ q.L * q.Δ ∧
    ⌈(2 : ℝ) ^ 30 * (1 + q.L * q.Δ / q.ε ^ 2) ^ 3 * (1 + q.σ ^ 2 / q.ε ^ 2)⌉₊ ≤ q.d
  admissible q f O := HolderNoiseNonconvex.spec.admissible q.toParams f O
  successful q f output P := HolderNoiseNonconvex.spec.successful q.toParams f output P

end LongTails.Setups.HolderNoiseNonconvexLower
