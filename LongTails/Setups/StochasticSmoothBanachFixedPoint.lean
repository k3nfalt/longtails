import LongTails.Setups.StochasticGeneralizedMonotone
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

open MeasureTheory

namespace LongTails.Setups.StochasticSmoothBanachFixedPoint

open OracleTemplate

def HasSmoothSquaredNorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ℝ) : Prop :=
  ∃ J : E → E →L[ℝ] ℝ, Continuous J ∧
    (∀ x, ‖J x‖ ≤ ‖x‖) ∧
    ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  x0 : E
  C : ℝ
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
  valid q := 1 ≤ q.C ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε ∧
    HasSmoothSquaredNorm q.E q.C
  admissible q T O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) ∧
    (∃ xstar, T xstar = xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure _) T g q.σ
  successful q T output P :=
    Measurable output ∧
    Integrable (fun ω => ‖T (output ω) - output ω‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖T (output ω) - output ω‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2

end LongTails.Setups.StochasticSmoothBanachFixedPoint
