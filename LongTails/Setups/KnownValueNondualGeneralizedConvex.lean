import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace LongTails.Setups.KnownValueNondualGeneralizedConvex

open OracleTemplate

structure Public where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  ε : ℝ
  fstar : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := ℝ × EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.d ∧ 0 < p.L0 ∧ 0 < p.L1 ∧ 0 < p.R ∧ 0 < p.ε
  admissible p f O :=
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Continuous (gradient f) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖gradient f z‖) '' segment ℝ x y)) * ‖x - y‖) ∧
    (∀ k seed x, O.answer k (0, x) seed = (f x, gradient f x)) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f xstar = p.fstar ∧
      ∑ i, |p.x0 i - xstar i| ≤ p.R)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧ f xstar = p.fstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.KnownValueNondualGeneralizedConvex
