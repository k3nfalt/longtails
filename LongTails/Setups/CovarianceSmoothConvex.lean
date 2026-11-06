import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.CovarianceSmoothConvex

open OracleTemplate

structure Params extends StochasticSmoothAndConvex.Params.{0} where
  [finiteDimensionalE : FiniteDimensional ℝ E]
  s : ℝ
  δ : ℝ

attribute [instance] Params.finiteDimensionalE

structure IsCovarianceGradient {E : Type*} {Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (f : E → ℝ)
    (g : E → Ω → E) (σ s : ℝ) : Prop
    extends StochasticSmoothAndConvex.IsStochasticGradient E Ω p f g σ where
  covariance : ∀ x v, (∫ ω, ⟪v, g x ω - gradient f x⟫ ^ 2 ∂p) ≤ s ^ 2 * ‖v‖ ^ 2

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 ≤ q.s ∧ q.s ≤ q.σ ∧
    0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    IsCovarianceGradient (p : Measure _) f g q.σ q.s
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.CovarianceSmoothConvex
