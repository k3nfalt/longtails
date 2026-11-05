import LongTails.Setups.StochasticFixedPointSmoothBanach
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.StochasticPowerSmoothFixedPoint

open OracleTemplate

structure Params extends StochasticFixedPointSmoothBanach.Params where
  exponent : ℝ

def PowerSmooth (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (s K : ℝ)
    (j : E → E →L[ℝ] ℝ) : Prop :=
  ∀ x y : E, ‖x + y‖ ^ s ≤ ‖x‖ ^ s + s * j x y + K * ‖y‖ ^ s

abbrev Model := StochasticFixedPointSmoothBanach.Model

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Model p.E p.Ξ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 1 < q.exponent ∧ q.exponent ≤ 2 ∧ 1 ≤ q.K ∧ 0 < q.D ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q M O :=
    ∃ P : ProbabilityMeasure (ℕ → q.Ξ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ξ) => ξ k)
        (M.law : Measure q.Ξ) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ξ
            law := P
            answer := fun _ (_, x) ξ => M.sample ξ x } ∧
      (∃ j : q.E → q.E →L[ℝ] ℝ, PowerSmooth q.E q.exponent q.K j) ∧
      (∀ x y, ‖M.map x - M.map y‖ ≤ ‖x - y‖) ∧
      (∃ xstar, M.map xstar = xstar ∧ ‖q.x0 - xstar‖ ≤ q.D) ∧
      Measurable (Function.uncurry M.sample) ∧
      (∀ x, Integrable (fun ξ => M.sample ξ x) (M.law : Measure q.Ξ) ∧
        ∫ ξ, M.sample ξ x ∂(M.law : Measure q.Ξ) = M.map x) ∧
      (∀ x, Integrable (fun ξ => ‖M.sample ξ x - M.map x‖ ^ q.exponent)
          (M.law : Measure q.Ξ) ∧
        ∫ ξ, ‖M.sample ξ x - M.map x‖ ^ q.exponent ∂(M.law : Measure q.Ξ) ≤
          q.σ ^ q.exponent)
  successful q M output P :=
    Measurable output ∧
      Integrable (fun ω => ‖output ω - M.map (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖output ω - M.map (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticPowerSmoothFixedPoint
