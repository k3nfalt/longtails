import LongTails.Setups.SmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace LongTails.Setups.MinimizerRegularHessian

open OracleTemplate

structure Params extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  [finiteE : FiniteDimensional ℝ E]
  [nontrivialE : Nontrivial E]
  μ : ℝ
  M : ℝ
  R : ℝ
  ε : ℝ

attribute [instance] Params.finiteE Params.nontrivialE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.M ∧ 0 < p.R ∧ 0 < p.ε
  admissible p f O :=
    Differentiable ℝ f ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ k x seed, O.answer k (0, x) seed = gradient f x) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R ∧
      ∀ x, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) xstar‖ ≤ p.M * ‖x - xstar‖)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.MinimizerRegularHessian
