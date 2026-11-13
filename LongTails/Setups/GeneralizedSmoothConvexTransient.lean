import LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Setups.GeneralizedSmoothConvexTransient

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  R : ℝ
  ε : ℝ

noncomputable abbrev Params.toRadiusOnly (p : Params) : RadiusOnlyGeneralizedSmoothConvex.Params :=
  { E := EuclideanSpace ℝ (Fin p.d), L0 := p.L0, L1 := p.L1, x0 := p.x0,
    R := p.R, ε := p.ε }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := id
  valid p := 0 < p.L0 ∧ 0 < p.L1 ∧ 0 < p.R ∧ 0 < p.ε ∧
    1048576 ≤ p.L1 * p.R ∧ p.L0 / p.L1 ^ 2 ≤ p.ε ∧ p.ε ≤ p.L0 * p.R ^ 2 / 16 ∧
    ⌈1048576 * (1 + p.L1 * p.R) ^ 8 * Real.exp (2 * Real.sqrt (p.L1 * p.R))⌉₊ ≤ p.d
  admissible p := RadiusOnlyGeneralizedSmoothConvex.spec.admissible p.toRadiusOnly
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GeneralizedSmoothConvexTransient
