import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import LongTails.Setups.EllSmoothNonconvex
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.StochasticEllSmoothNonconvex

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
  ℓ : ℝ → ℝ
  ρ : ℝ
  p : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 ≤ q.ρ ∧ q.ρ < 2 ∧ LongTails.Setups.EllSmoothNonconvex.Regular q.ℓ q.ρ ∧
    1 < q.p ∧ q.p ≤ 2 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      Differentiable ℝ (gradient f) ∧
      (∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ q.ℓ ‖gradient f x‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (ν : Measure _)) ∧
      (∀ x, ∫ ω, g x ω ∂(ν : Measure _) = gradient f x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) (ν : Measure _)) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂(ν : Measure _) ≤ q.σ ^ q.p)
  successful q f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.StochasticEllSmoothNonconvex
