import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory

namespace LongTails.Setups.SlidingStochasticComposite

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
  ℓ : ℝ
  L : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.borelE Params.measurableΩ

structure Instance (p : Params) where
  f : p.E → ℝ
  h : p.E → ℝ

noncomputable def objective {p : Params} (I : Instance p) (x : p.E) : ℝ := I.f x + I.h x

noncomputable def moreauGap {p : Params} (I : Instance p) (x : p.E) : ℝ :=
  objective I x - ⨅ y, (objective I y + p.ℓ * ‖y - x‖ ^ 2)

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.ℓ ∧ 0 ≤ p.L ∧ 0 ≤ p.σ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p I O :=
    ∃ (g : p.E → p.Ω → p.E) (μ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure p.Ω) (P : Measure (ℕ → p.Ω)) ∧
      O = { Seed := fun _ => p.Ω
            law := P
            answer := fun _ q ω => if q.1 = 0 then gradient I.f q.2 else g q.2 ω } ∧
      (∀ x, HasGradientAt I.f (gradient I.f x) x) ∧
      (∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.ℓ * ‖x - y‖) ∧
      ConvexOn ℝ Set.univ I.h ∧
      (∀ x, HasGradientAt I.h (gradient I.h x) x) ∧
      (∀ x y, ‖gradient I.h x - gradient I.h y‖ ≤ p.L * ‖x - y‖) ∧
      (∃ lower : ℝ, (∀ x, lower ≤ objective I x) ∧ objective I p.x0 - lower ≤ p.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (μ : Measure p.Ω)) ∧
      (∀ x, ∫ ω, g x ω ∂(μ : Measure p.Ω) = gradient I.h x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient I.h x‖ ^ 2) (μ : Measure p.Ω)) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient I.h x‖ ^ 2 ∂(μ : Measure p.Ω) ≤ p.σ ^ 2)
  successful p I output P :=
    Measurable output ∧
      Integrable (fun ω => moreauGap I (output ω)) (P : Measure _) ∧
      ∫ ω, moreauGap I (output ω) ∂(P : Measure _) ≤ p.ε ^ 2 / (8 * p.ℓ)

end LongTails.Setups.SlidingStochasticComposite
