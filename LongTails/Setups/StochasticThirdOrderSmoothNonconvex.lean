import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory

namespace LongTails.Setups.StochasticThirdOrderSmoothNonconvex

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L₁ : ℝ
  L₂ : ℝ
  L₃ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE Params.borelE
  Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L₁ ∧ 0 < q.L₂ ∧ 0 < q.L₃ ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (μ : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      ContDiff ℝ 3 f ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L₁ * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ q.L₂ * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤
        q.L₃ * ‖x - y‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (μ : Measure _)) ∧
      (∀ x, ∫ ω, g x ω ∂(μ : Measure _) = gradient f x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (μ : Measure _)) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(μ : Measure _) ≤ q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticThirdOrderSmoothNonconvex
