import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.ParameterFreeHeavyTailedSmooth

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.completeE Public.measurableE
  Public.borelE Public.countableE

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  Δ : ℝ
  σ : ℝ
  p : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q.toPublic
  valid q := 0 < q.L ∧ 0 < q.Δ ∧ 0 ≤ q.σ ∧ 1 < q.p ∧ q.p ≤ 2 ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) ω => g x ω } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (ν : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(ν : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) (ν : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂(ν : Measure _) ≤ q.σ ^ q.p)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.ParameterFreeHeavyTailedSmooth
