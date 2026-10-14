import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.ScalarHolderStochastic

open OracleTemplate

structure Params where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  H : ℝ
  ν : ℝ
  Δ : ℝ
  σ : ℝ
  p : ℝ
  ε : ℝ
  x0 : ℝ

attribute [instance] Params.measurableΩ

structure IsGradientOracle {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (g : ℝ → Ω → ℝ) (σ p : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) μ
  unbiased : ∀ x, ∫ ω, g x ω ∂μ = deriv f x
  moment_integrable : ∀ x, Integrable (fun ω => |g x ω - deriv f x| ^ p) μ
  moment : ∀ x, (∫ ω, |g x ω - deriv f x| ^ p ∂μ) ≤ σ ^ p

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance _ := ℝ → ℝ
  Query _ := ℝ
  Reply _ := ℝ
  Output _ := ℝ
  publicInput p := p
  valid q := 0 < q.H ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 < q.Δ ∧
    0 ≤ q.σ ∧ 1 < q.p ∧ q.p ≤ 2 ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : ℝ → q.Ω → ℝ) (μ : ProbabilityMeasure q.Ω)
        (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasDerivAt f (deriv f x) x) ∧
      (∀ x y, |deriv f x - deriv f y| ≤ q.H * |x - y| ^ q.ν) ∧
      (∃ lower, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ) ∧
      IsGradientOracle (μ : Measure _) f g q.σ q.p
  successful q f output P :=
    Measurable output ∧
      (P : Measure _) {ω | q.ε < |deriv f (output ω)|} ≤ ENNReal.ofReal (1 / 3 : ℝ)

end LongTails.Setups.ScalarHolderStochastic
