import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.VarianceOnlySecondOrder

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
  L : ℝ
  ρ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.borelE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 < q.ρ ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1 ∧
    q.ρ * q.ε ≤ q.L ^ 2 ∧ 0 < Module.finrank ℝ q.E
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (P0 : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ContDiff ℝ 2 f ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ q.ρ * ‖x - y‖) ∧
    (∀ x, f q.x0 - f x ≤ q.Δ) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure _) ≤ q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧
      ENNReal.ofReal (1 - q.δ) ≤ (P : Measure _) {ω |
        ‖gradient f (output ω)‖ ≤ q.ε ∧
        ∀ v, -Real.sqrt (q.ρ * q.ε) * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient f) (output ω) v⟫}

end LongTails.Setups.VarianceOnlySecondOrder
