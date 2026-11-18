import LongTails.Template
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.PointwiseHessianStationarity

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  L₀ : ℝ
  L₁ : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)
abbrev Reply (p : Params) := ℝ × Point p × (Point p →L[ℝ] Point p)

abbrev broadSpec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p → ℝ
  Query := Point
  Reply := Reply
  Output := Point
  publicInput p := p
  valid p := 0 ≤ p.L₀ ∧ 0 ≤ p.L₁ ∧ 0 < p.L₀ + p.L₁ ∧ 0 < p.Δ ∧ 0 ≤ p.G ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 3 f ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖) ∧
    (∀ x, f 0 - f x ≤ p.Δ) ∧
    ‖gradient f 0‖ ≤ p.G ∧
    (∀ history seed x, O.answer history (0, x) seed =
      (f x, gradient f x, fderiv ℝ (gradient f) x))
  successful p f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
    (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _)) ≤ p.ε

abbrev spec : Setup := { broadSpec with
  valid := fun p => broadSpec.valid p ∧ 16 * p.ε ≤ p.G ∧
    2 ^ 39 ≤ p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε) ∧
    2 ^ 140 * (1 + ⌈p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)⌉₊) ^ 4 ≤ p.d }

end LongTails.Setups.PointwiseHessianStationarity
