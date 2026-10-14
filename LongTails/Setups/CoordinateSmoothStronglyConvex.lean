import LongTails.Template
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Algebra.Order.Floor.Ring

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.CoordinateSmoothStronglyConvex

open OracleTemplate

structure Params where
  d : ℕ
  [nonzero : NeZero d]
  L : Fin d → ℝ
  μ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := Fin p.d × EuclideanSpace ℝ (Fin p.d)
  Reply _ := ℝ
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.μ ∧ (∀ i, p.μ ≤ p.L i) ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ k seed i x, oracle.answer k (0, (i, x)) seed = gradient f x i) ∧
    (∀ x i t, f (x + EuclideanSpace.single i t) ≤
      f x + t * gradient f x i + p.L i / 2 * t ^ 2) ∧
    (∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ)
  successful p f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.CoordinateSmoothStronglyConvex
