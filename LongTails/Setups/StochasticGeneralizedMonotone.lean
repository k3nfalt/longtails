import LongTails.Setups.GeneralizedLipschitzMonotone
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticGeneralizedMonotone

open OracleTemplate

structure Params extends LongTails.Setups.GeneralizedLipschitzMonotone.Public where
  [finiteE : FiniteDimensional ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  R : ℝ
  σ : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Params.finiteE Params.completeE Params.measurableE Params.borelE
  Params.countableE Params.measurableΩ

structure IsStochasticOperator {E Ω : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (F : E → E) (g : E → Ω → E)
    (σ : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, (∫ ω, g x ω ∂p) = F x
  variance_integrable : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) p
  variance : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂p) ≤ σ ^ 2

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 ≤ q.L0 ∧ 0 ≤ q.L1 ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧
    0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q F O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    Continuous F ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    (∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    IsStochasticOperator (p : Measure _) F g q.σ
  successful q F output P :=
    Measurable output ∧
      (P : Measure _) {ω | q.ε < ‖F (output ω)‖} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.StochasticGeneralizedMonotone
