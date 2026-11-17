import LongTails.Setups.GeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  R : ℝ
  Δ : ℝ
  ε : ℝ

noncomputable abbrev Params.toGeneralized (p : Params) : GeneralizedSmoothAndConvex.Params :=
  { E := EuclideanSpace ℝ (Fin p.d), L0 := p.L0, L1 := p.L1, R := p.R, Δ := p.Δ, x0 := p.x0,
    ε := p.ε }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := id
  valid p := 0 < p.L0 ∧ 0 < p.L1 ∧ 0 < p.R ∧ 0 < p.ε ∧
    16 * p.ε ≤ p.L0 * p.R ^ 2 ∧ 1048576 ≤ p.L1 * p.R ∧
    p.ε * (2 + p.L1 * p.R) ^ 2 ≤ p.Δ ∧ p.ε * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) ≤ p.Δ ∧
    ⌈70368744177664 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 6⌉₊ ≤ p.d
  admissible p := GeneralizedSmoothAndConvex.spec.admissible p.toGeneralized
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
