import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.DiagonalSmoothStronglyConvex

open OracleTemplate

structure Public where
  d : ℕ
  [nonzero : NeZero d]
  x0 : EuclideanSpace ℝ (Fin d)
  fstar : ℝ

attribute [instance] Public.nonzero

structure Params extends Public where
  w : Fin d → ℝ
  μ : ℝ
  Δ : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := ℝ × EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput := Params.toPublic
  valid q := 0 < q.μ ∧ q.μ ≤ 1 ∧ (∀ i, 0 < q.w i) ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ k seed x, oracle.answer k (0, x) seed = (f x, gradient f x)) ∧
    (∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + (∑ i, q.w i * (y i - x i) ^ 2) / 2) ∧
    (∀ x y, f x + ⟪gradient f x, y - x⟫ + q.μ * (∑ i, q.w i * (y i - x i) ^ 2) / 2 ≤ f y) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f xstar = q.fstar) ∧
    f q.x0 - q.fstar ≤ q.Δ
  successful q f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧ f xstar = q.fstar ∧
      ∀ᵐ ω ∂(P : Measure _), f (output ω) - f xstar ≤ q.ε

end LongTails.Setups.DiagonalSmoothStronglyConvex
