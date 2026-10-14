import LongTails.Setups.GeneralizedSmoothAndConvex
import LongTails.Setups.StochasticSmoothAndConvex
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open OracleTemplate

structure IID {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ξ : ℕ → Ξ → Ω) (p : Measure Ω) (P : Measure Ξ) : Prop where
  measurable : ∀ k, Measurable (ξ k)
  independent : iIndepFun ξ P
  marginal : ∀ k, P.map (ξ k) = p

structure IsLightTailGradient (E : Type*) (Ω : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (f : E → ℝ) (oracle : E → Ω → E) (σ : ℝ)
    : Prop extends LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient E Ω p f oracle σ where
  exponential_integrable : ∀ x,
    Integrable (fun ω => Real.exp (‖oracle x ω - gradient f x‖^2 / σ^2)) p
  exponential : ∀ x,
    (∫ ω, Real.exp (‖oracle x ω - gradient f x‖^2 / σ^2) ∂p) ≤ Real.exp 1

structure Params extends LongTails.Setups.GeneralizedSmoothAndConvex.Public where
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  σ : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Params.measurableE Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 < q.Δ ∧
    0 ≤ q.σ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    IID (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ q.L0 + q.L1 * ‖gradient f x‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0-xstar‖ ≤ q.R ∧ f q.x0-f xstar ≤ q.Δ) ∧
    IsLightTailGradient q.E q.Ω (p : Measure _) f g q.σ
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.StochasticGeneralizedSmoothAndConvex
