import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.SpikedSubGaussianConvex

open OracleTemplate

structure Params where
  m : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  G : ℝ
  R : ℝ
  vTop : ℝ
  vRest : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev Space (q : Params) := EuclideanSpace ℝ (Fin (q.m + 1))

noncomputable def varianceProxy (q : Params) (u : Space q) : ℝ :=
  q.vRest * ‖u‖ ^ 2 + (q.vTop - q.vRest) * (u 0) ^ 2

structure IsSubGaussianSubgradient (q : Params) (p : Measure q.Ω)
    [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, (∫ ω, g x ω ∂p) = v x
  support : ∀ x y, ⟪v x, y - x⟫ ≤ f y - f x
  exponential_integrable : ∀ x u t,
    Integrable (fun ω => Real.exp (t * ⟪g x ω - v x, u⟫)) p
  exponential_bound : ∀ x u t,
    (∫ ω, Real.exp (t * ⟪g x ω - v x, u⟫) ∂p) ≤
      Real.exp (t ^ 2 * varianceProxy q u / 2)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Space q → ℝ
  Query q := Space q
  Reply q := Space q
  Output q := Space q
  publicInput q := q
  valid q := 0 < q.G ∧ 0 < q.R ∧ 0 ≤ q.vRest ∧ q.vRest ≤ q.vTop ∧ 0 < q.ε
  admissible q f O :=
    ∃ (v : Space q → Space q) (g : Space q → q.Ω → Space q)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x y, |f x - f y| ≤ q.G * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖xstar‖ ≤ q.R) ∧
    IsSubGaussianSubgradient q (p : Measure _) f v g
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ (1 / 3 : ENNReal)

end LongTails.Setups.SpikedSubGaussianConvex
