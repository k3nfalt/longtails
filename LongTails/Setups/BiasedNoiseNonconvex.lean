import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.BiasedNoiseNonconvex

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  m : ℝ
  M : ℝ
  σ : ℝ
  ζ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.m ∧ q.m < 1 ∧ 0 ≤ q.M ∧ 0 ≤ q.σ ∧ 0 ≤ q.ζ ∧ 0 ≤ q.Δ ∧ 0 < q.ε ∧
    16 * q.ζ ^ 2 ≤ (1 - q.m) * q.ε ^ 2
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
      (fstar : ℝ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, fstar ≤ f x) ∧ (∀ η, 0 < η → ∃ x, f x < fstar + η) ∧ f q.x0 - fstar ≤ q.Δ ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ‖(∫ ω, g x ω ∂p) - gradient f x‖ ^ 2 ≤ q.m * ‖gradient f x‖ ^ 2 + q.ζ ^ 2) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - ∫ ω', g x ω' ∂p‖ ^ 2) p) ∧
      (∀ x, ∫ ω, ‖g x ω - ∫ ω', g x ω' ∂p‖ ^ 2 ∂p ≤ q.M * ‖∫ ω, g x ω ∂p‖ ^ 2 + q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.BiasedNoiseNonconvex
