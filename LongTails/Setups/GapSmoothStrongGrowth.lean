import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.GapSmoothStrongGrowth

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [countableE : SecondCountableTopology E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  H0 : ℝ
  H1 : ℝ
  R : ℝ
  Δ : ℝ
  ρ : ℝ
  ε : ℝ
  δ : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.countableE
  Params.measurableE Params.borelE Params.measurableΩ

structure IsStrongGrowthOracle {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (f : E → ℝ)
    (g : E → Ω → E) (ρ : ℝ) : Prop where
  measurable : Measurable (fun z : E × Ω => g z.1 z.2)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, (∫ ω, g x ω ∂p) = gradient f x
  integrable_variance : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  variance : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p) ≤
    (ρ - 1) * ‖gradient f x‖ ^ 2

def GapUpperModel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (u : E) (H0 H1 : ℝ) : Prop :=
  ∀ x y, (2 * Real.sqrt 3 + Real.sqrt 6) * Real.sqrt H1 * ‖y - x‖ ≤ 1 →
    f y ≤ f x + ⟪gradient f x, y - x⟫ + (H0 + H1 * (f x - f u)) * ‖y - x‖ ^ 2

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 ≤ q.H0 ∧ 0 ≤ q.H1 ∧ 0 < q.R ∧ 0 < q.Δ ∧
    1 ≤ q.ρ ∧ 0 < q.ε ∧ q.ε ≤ q.Δ ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      f q.x0 - f xstar ≤ q.Δ ∧ GapUpperModel f xstar q.H0 q.H1) ∧
    IsStrongGrowthOracle (p : Measure _) f g q.ρ
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (∫ ω, (if q.ε < f (output ω) - f xstar then (1 : ℝ) else 0) ∂(P : Measure _)) ≤ q.δ

end LongTails.Setups.GapSmoothStrongGrowth
