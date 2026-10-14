import LongTails.Setups.SmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Setups.RelativeErrorSmoothConvex

open OracleTemplate

structure Public extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public where
  α : ℝ
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := fun p => p
  valid p := 0 < p.L ∧ 0 ≤ p.α ∧ p.α < 1 ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, f x + ⟪gradient f x, y - x⟫ ≤ f y) ∧
    (∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + p.L / 2 * ‖y - x‖ ^ 2) ∧
    (∀ k x seed, ‖oracle.answer k (0, x) seed - gradient f x‖ ≤ p.α * ‖gradient f x‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.RelativeErrorSmoothConvex
