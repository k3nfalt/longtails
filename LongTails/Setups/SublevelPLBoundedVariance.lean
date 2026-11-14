import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.SublevelPLBoundedVariance

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  L : ℝ
  τ : ℝ
  α : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.finiteE Public.measurableE Public.borelE

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p.toPublic
  valid p := 0 < p.L ∧ 0 < p.τ ∧ 1 ≤ p.α ∧ p.α < 2 ∧ 0 ≤ p.σ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ∃ (g : p.E → p.Ω → p.E) (P0 : ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (ℕ → p.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → p.Ω) => ξ k)
      (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    BddBelow (Set.range f) ∧
    (∀ x, f x ≤ f p.x0 → f x - (⨅ y, f y) ≤ p.τ * ‖gradient f x‖ ^ p.α) ∧
    f p.x0 - (⨅ y, f y) ≤ p.Δ ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure _) ≤ p.σ ^ 2)
  successful p f output P :=
    Integrable (fun ω => f (output ω) - ⨅ y, f y) (P : Measure _) ∧
      (∫ ω, f (output ω) - ⨅ y, f y ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.SublevelPLBoundedVariance
