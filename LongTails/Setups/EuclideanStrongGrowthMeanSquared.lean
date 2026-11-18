import LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Setups.EuclideanStrongGrowthMeanSquared

open OracleTemplate

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  Lbar : ℝ
  Γ : ℝ
  R : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

noncomputable abbrev Params.toBase (q : Params) : StrongGrowthMeanSquaredSmoothConvex.Params :=
  { E := EuclideanSpace ℝ (Fin q.d), measurableE := borel _,
    borelE := @BorelSpace.mk (EuclideanSpace ℝ (Fin q.d)) _ (borel _) rfl, Ω := q.Ω,
    Lbar := q.Lbar, Γ := q.Γ, R := q.R, ε := q.ε, x0 := q.x0 }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput := id
  valid q := 0 < q.Lbar ∧ 0 ≤ q.Γ ∧ 0 < q.R ∧ 0 < q.ε ∧
    67108864 * Real.sqrt (1 + q.Γ ^ 2) * q.ε ≤ q.Lbar * q.R ^ 2 ∧
    (q.Lbar * q.R ^ 2 / (Real.sqrt (1 + q.Γ ^ 2) * q.ε)) ^ 3 ≤ q.d ∧
    ∃ a b : q.Ω, a ≠ b ∧ MeasurableSet ({a} : Set q.Ω) ∧ MeasurableSet ({b} : Set q.Ω)
  admissible q := StrongGrowthMeanSquaredSmoothConvex.spec.admissible q.toBase
  successful q := StrongGrowthMeanSquaredSmoothConvex.spec.successful q.toBase

end LongTails.Setups.EuclideanStrongGrowthMeanSquared
