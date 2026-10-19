import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.CurvatureAlignedNoiseNonconvex

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
  Lg : ℝ
  Lξ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
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
  valid q := 0 < q.Lg ∧ 0 ≤ q.Lξ ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (P0 : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
      (Q : q.E → q.E →L[ℝ] q.E),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x u, f (x + u) ≤ f x + ⟪gradient f x, u⟫ + ⟪Q x u, u⟫ / 2) ∧
    (∀ x, ⟪Q x (gradient f x), gradient f x⟫ ≤ q.Lg * ‖gradient f x‖ ^ 2) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure _) ≤ q.σ ^ 2) ∧
    (∀ x, Integrable (fun ω => ⟪Q x (g x ω - gradient f x), g x ω - gradient f x⟫)
      (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ⟪Q x (g x ω - gradient f x), g x ω - gradient f x⟫ ∂(P0 : Measure _) ≤
      q.Lξ * ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure _))
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.CurvatureAlignedNoiseNonconvex
