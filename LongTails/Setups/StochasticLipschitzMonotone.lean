import LongTails.Setups.StochasticGeneralizedMonotone

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticLipschitzMonotone

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  x0 : E
  L : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.linearE Params.finiteE Params.completeE
  Params.measurableE Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q F O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    (∀ x y, ‖F x - F y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure _) F g q.σ
  successful q F output P :=
    Measurable output ∧
      Integrable (fun ω => ‖F (output ω)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖F (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2

end LongTails.Setups.StochasticLipschitzMonotone
