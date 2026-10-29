import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.CovarianceBoundedConvex

open OracleTemplate

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev Space (q : Params) := EuclideanSpace ℝ (Fin q.d)


structure IsCovarianceSubgradient (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, (∫ ω, g x ω ∂p) = v x
  support : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x
  variance_integrable : ∀ x, Integrable (fun ω => ‖g x ω-v x‖^2) p
  covariance : ∀ x u, (∫ ω, ⟪g x ω-v x, u⟫^2 ∂p) ≤ q.σ^2*‖u‖^2/q.d

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Space q → ℝ
  Query q := Space q
  Reply q := Space q
  Output q := Space q
  publicInput q := q
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 < q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (v : Space q → Space q) (g : Space q → q.Ω → Space q) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x y, |f x - f y| ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖xstar‖ ≤ q.R) ∧
    IsCovarianceSubgradient q (p : Measure _) f v g
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ (1 / 3 : ENNReal)

end LongTails.Setups.CovarianceBoundedConvex
