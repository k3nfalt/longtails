import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory

namespace LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex

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
  Lbar : ℝ
  Γ : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E × p.E
  Reply p := p.E × p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.Lbar ∧ 0 ≤ q.Γ ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ q.Γ ^ 2 * ‖gradient f x‖ ^ 2) ∧
      (∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) p) ∧
      (∀ x y, ∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p ≤ q.Lbar ^ 2 * ‖x - y‖ ^ 2)
  successful q f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f Set.univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        ∫ ω, f (output ω) - f xstar ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex
