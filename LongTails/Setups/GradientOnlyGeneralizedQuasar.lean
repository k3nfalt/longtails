import LongTails.Setups.GeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.GradientOnlyGeneralizedQuasar

open OracleTemplate

structure Params extends GeneralizedSmoothAndConvex.Public.{0} where
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  γ : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Params.finiteE Params.measurableE Params.borelE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 < p.R ∧ 0 < p.Δ ∧
    0 < p.γ ∧ p.γ ≤ 1 ∧ 0 < p.ε ∧ 0 < p.δ ∧ p.δ < 1
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Continuous (gradient f) ∧
    (∀ history x seed, O.answer history (0, x) seed = gradient f x) ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖gradient f (x + θ • (y - x))‖ ≤ M) →
      ‖gradient f x - gradient f y‖ ≤ (p.L0 + p.L1 * M) * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R ∧
      f p.x0 - f xstar ≤ p.Δ ∧
      ∀ x, p.γ * (f x - f xstar) ≤ ⟪gradient f x, x - xstar⟫)
  successful p f output P :=
    ∃ xstar, IsMinOn f univ xstar ∧
      (P : Measure _) {ω | p.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal p.δ

end LongTails.Setups.GradientOnlyGeneralizedQuasar
