import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

open MeasureTheory

namespace LongTails.Setups.StochasticFixedPointSmoothBanach

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [spaceE : NormedSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ξ : Type
  [measurableΞ : MeasurableSpace Ξ]
  K : ℝ
  D : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.spaceE Params.completeE Params.measurableE Params.borelE
  Params.countableE Params.measurableΞ

def TwoUniformlySmooth (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ℝ)
    (j : E → E →L[ℝ] ℝ) : Prop :=
  ∀ x y : E, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * j x y + K * ‖y‖ ^ 2

structure Model (E Ξ : Type*) [MeasurableSpace Ξ] where
  law : ProbabilityMeasure Ξ
  map : E → E
  sample : Ξ → E → E

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Model p.E p.Ξ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 ≤ q.K ∧ 0 < q.D ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q M O :=
    ∃ P : ProbabilityMeasure (ℕ → q.Ξ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ξ) => ξ k)
        (M.law : Measure q.Ξ) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ξ
            law := P
            answer := fun _ (_, x) ξ => M.sample ξ x } ∧
      (∃ j : q.E → q.E →L[ℝ] ℝ, TwoUniformlySmooth q.E q.K j) ∧
      (∀ x y, ‖M.map x - M.map y‖ ≤ ‖x - y‖) ∧
      (∃ xstar, M.map xstar = xstar ∧ ‖q.x0 - xstar‖ ≤ q.D) ∧
      Measurable (Function.uncurry M.sample) ∧
      (∀ x, Integrable (fun ξ => M.sample ξ x) (M.law : Measure q.Ξ) ∧
        ∫ ξ, M.sample ξ x ∂(M.law : Measure q.Ξ) = M.map x) ∧
      (∀ x, Integrable (fun ξ => ‖M.sample ξ x - M.map x‖ ^ 2) (M.law : Measure q.Ξ) ∧
        ∫ ξ, ‖M.sample ξ x - M.map x‖ ^ 2 ∂(M.law : Measure q.Ξ) ≤ q.σ ^ 2)
  successful q M output P :=
    Measurable output ∧
      Integrable (fun ω => ‖output ω - M.map (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖output ω - M.map (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticFixedPointSmoothBanach
