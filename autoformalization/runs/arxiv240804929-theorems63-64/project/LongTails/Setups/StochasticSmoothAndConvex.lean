import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.Convex.Function

open MeasureTheory

namespace LongTails.Setups.StochasticSmoothAndConvex

open OracleTemplate

section

variable (E : Type*) (Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]

structure IsStochasticGradient (p : Measure Ω) [IsProbabilityMeasure p]
    (f : E → ℝ) (oracle : E → Ω → E) (σ : ℝ) : Prop where
  measurable : Measurable (Function.uncurry oracle)
  integrable : ∀ x, Integrable (oracle x) p
  unbiased : ∀ x, ∫ ω, oracle x ω ∂p = gradient f x
  variance_integrable : ∀ x, Integrable (fun ω => ‖oracle x ω-gradient f x‖^2) p
  variance : ∀ x, ∫ ω, ‖oracle x ω-gradient f x‖^2 ∂p ≤ σ^2

end

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (oracle : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω),
    O = { Seed := fun _ => q.Ω
          law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)), inferInstance⟩
          answer := fun _ (_, x) seed => oracle x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    IsStochasticGradient q.E q.Ω p f oracle q.σ
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.StochasticSmoothAndConvex
