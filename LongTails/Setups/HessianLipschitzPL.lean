import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace LongTails.Setups.HessianLipschitzPL

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  H : ℝ
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.finiteE Public.measurableE

structure Params extends Public where
  μ : ℝ
  Δ : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := ℝ × p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.H ∧ 0 < p.μ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.H * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ ∧
      ∀ x, 2 * p.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) ∧
    (∀ history seed x, O.answer history (0, x) seed =
      (f x, gradient f x, fderiv ℝ (gradient f) x))
  successful p f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f Set.univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        ∫ ω, f (output ω) - f xstar ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.HessianLipschitzPL
