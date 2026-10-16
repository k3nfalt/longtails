import LongTails.Setups.SmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.RelativeGradientStrongQuasar

open OracleTemplate

structure Params extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  μ : ℝ
  γ : ℝ
  δ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.finiteE Params.measurableE Params.borelE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.μ ∧ 0 < p.γ ∧ p.γ ≤ 1 ∧
    0 ≤ p.δ ∧ p.δ < 1 ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ g : p.E → p.E, Measurable g ∧
      (∀ k x seed, O.answer k (0, x) seed = g x) ∧
      ∀ x, ‖g x - gradient f x‖ ≤ p.δ * ‖gradient f x‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ ∧
      ∀ x, p.γ * f x + ⟪gradient f x, xstar - x⟫ +
        p.γ * p.μ / 2 * ‖xstar - x‖ ^ 2 ≤ p.γ * f xstar)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.RelativeGradientStrongQuasar
