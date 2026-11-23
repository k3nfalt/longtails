import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace LongTails.Setups.EllSmoothNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  ℓ : ℝ → ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

def Regular (ℓ : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ u v, 0 ≤ u → u ≤ v → ℓ u ≤ ℓ v) ∧
  (∀ u v, 0 < u → u ≤ v → ℓ v * u ^ ρ ≤ ℓ u * v ^ ρ) ∧
  ∀ u, 0 < u → 0 < ℓ u

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p → ℝ
  Query := Point
  Reply p := ℝ × Point p
  Output := Point
  publicInput p := p
  valid p := 0 ≤ p.ρ ∧ p.ρ ≤ 2 ∧ Regular p.ℓ p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.ℓ ‖gradient f x‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    (∀ history seed x, O.answer history (0, x) seed = (f x, gradient f x))
  successful p f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
    (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.EllSmoothNonconvex
