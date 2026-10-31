import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.AffineMomentConvex

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
  L : ℝ
  R : ℝ
  σ : ℝ
  σ0 : ℝ
  α : ℝ
  ε : ℝ
  δ : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.countableE
  Params.measurableE Params.borelE Params.measurableΩ

structure IsFiniteMomentOracle {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (f : E → ℝ)
    (g : E → Ω → E) (α σ σ0 : ℝ) : Prop where
  measurable : Measurable (fun z : E × Ω => g z.1 z.2)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, (∫ ω, g x ω ∂p) = gradient f x
  integrable_moment : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ α) p
  moment : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ α ∂p) ≤
    σ0 ^ α + σ ^ α * ‖gradient f x‖ ^ α

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 < q.R ∧ 0 ≤ q.σ ∧ 0 ≤ q.σ0 ∧ 1 < q.α ∧ q.α ≤ 2 ∧
    0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    IsFiniteMomentOracle (p : Measure _) f g q.α q.σ q.σ0
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (∫ ω, (if q.ε < f (output ω) - f xstar then (1 : ℝ) else 0) ∂(P : Measure _)) ≤ q.δ

end LongTails.Setups.AffineMomentConvex
