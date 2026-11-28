import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.HeavyTailedHighProbabilityStationarity

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
  p : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L ∧ 1 < q.p ∧ q.p ≤ 2 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε ∧ 0 < q.δ ∧
    q.δ ≤ 1 / 4
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (μ : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
      (fstar : ℝ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, fstar ≤ f x) ∧ (∀ η, 0 < η → ∃ x, f x < fstar + η) ∧ f q.x0 - fstar ≤ q.Δ ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) μ) ∧
      (∀ x, ∫ ω, g x ω ∂μ = gradient f x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) μ) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂μ ≤ q.σ ^ q.p)
  successful q f output P :=
    Measurable output ∧
      1 - q.δ ≤ (P : Measure _).real {ω | ‖gradient f (output ω)‖ ≤ q.ε}

end LongTails.Setups.HeavyTailedHighProbabilityStationarity
