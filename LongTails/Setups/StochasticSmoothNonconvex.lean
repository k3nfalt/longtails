import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory

namespace LongTails.Setups.StochasticSmoothNonconvex

open OracleTemplate

structure IID {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ξ : ℕ → Ξ → Ω) (p : Measure Ω) (P : Measure Ξ) : Prop where
  measurable : ∀ k, Measurable (ξ k)
  independent : ProbabilityTheory.iIndepFun ξ P
  marginal : ∀ k, P.map (ξ k) = p

structure StochasticGradient (E Ω : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (f : E → ℝ)
    (g : E → Ω → E) (σ : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  variance_integrable : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  variance : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2

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
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE
  Params.measurableE Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.Δ ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ) ∧
    StochasticGradient q.E q.Ω (p : Measure _) f g q.σ
  successful q f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2

end LongTails.Setups.StochasticSmoothNonconvex
