import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.HeavyTailedStrongGrowthConvex

open OracleTemplate
open StochasticGeneralizedSmoothAndConvex

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  R : ℝ
  ρ : ℝ
  p : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

structure IsRelativeMomentOracle {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : E → ℝ) (g : E → Ω → E)
    (p ρ : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) μ
  unbiased : ∀ x, ∫ ω, g x ω ∂μ = gradient f x
  moment_integrable : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p) μ
  moment : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ p ∂μ) ≤ ρ * ‖gradient f x‖ ^ p

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.ρ ∧ 1 < q.p ∧ q.p ≤ 2 ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (μ : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    IID (fun k (ξ : ℕ → q.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    IsRelativeMomentOracle (μ : Measure _) f g q.p q.ρ
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.HeavyTailedStrongGrowthConvex
