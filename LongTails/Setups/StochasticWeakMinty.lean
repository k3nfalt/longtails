import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticWeakMinty

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
  ρ : ℝ
  σ : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.ρ ∧ p.ρ ≤ 1 / (20 * p.L) ∧ 0 ≤ p.σ ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p F O :=
    ∃ (g : p.E → p.Ω → p.E) (μ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x y, ‖F x - F y‖ ≤ p.L * ‖x - y‖) ∧
      (∃ xstar, F xstar = 0 ∧ ‖xstar - p.x0‖ ≤ p.R ∧
        ∀ x, -p.ρ * ‖F x‖ ^ 2 ≤ ⟪F x, x - xstar⟫) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (μ : Measure _)) ∧
      (∀ x, ∫ ω, g x ω ∂(μ : Measure _) = F x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) (μ : Measure _)) ∧
      (∀ x, ∫ ω, ‖g x ω - F x‖ ^ 2 ∂(μ : Measure _) ≤ p.σ ^ 2)
  successful p F output P :=
    Integrable (fun ω => ‖F (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖F (output ω)‖ ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.StochasticWeakMinty
