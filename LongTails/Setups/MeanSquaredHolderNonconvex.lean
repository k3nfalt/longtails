import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.MeanSquaredHolderNonconvex

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
  L : ℝ
  M : ℝ
  ν : ℝ
  σ : ℝ
  Δ : ℝ
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
  valid q := 0 < q.L ∧ 0 ≤ q.M ∧ 1 / 2 ≤ q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ q.σ ^ 2) ∧
      (∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) p) ∧
      (∀ x y, ∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p ≤ q.M * ‖x - y‖ ^ (2 * q.ν))
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.MeanSquaredHolderNonconvex
