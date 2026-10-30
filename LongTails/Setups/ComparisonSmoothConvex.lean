import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LongTails.Setups.ComparisonSmoothConvex

open OracleTemplate

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure Params where
  n : ℕ
  L : ℝ
  R : ℝ
  ε : ℝ
  x0 : Point n

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.n → ℝ
  Query p := Point p.n × Point p.n
  Reply _ := Bool
  Output p := Point p.n
  publicInput p := p
  valid q := 1 ≤ q.n ∧ 0 < q.L ∧ 0 < q.R ∧ 0 < q.ε
  admissible q f O :=
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    (∀ history query seed, O.answer history query seed = decide (f query.2.1 ≤ f query.2.2))
  successful q f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ q.ε

end LongTails.Setups.ComparisonSmoothConvex
