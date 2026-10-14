import LongTails.Algorithms.ScheduledSgd
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.HeavyTailedPL

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  L : ℝ
  μ : ℝ
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.completeE Public.measurableE
  Public.borelE Public.countableE

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  σ : ℝ
  ν : ℝ
  q : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p.toPublic
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.σ ∧ 0 < p.ν ∧ 2 < p.q ∧ 0 ≤ p.Δ ∧
    0 < p.ε ∧ 0 < p.δ ∧ p.δ < 1
  admissible p f O :=
    ∃ (g : p.E → p.Ω → p.E) (P0 : ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (ℕ → p.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    BddBelow (Set.range f) ∧
    (∀ x, 2 * p.μ * (f x - ⨅ y, f y) ≤ ‖gradient f x‖ ^ 2) ∧
    f p.x0 - (⨅ y, f y) ≤ p.Δ ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure _) ≤ p.σ ^ 2) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p.q) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ p.q ∂(P0 : Measure _) ≤ p.ν ^ p.q)
  successful p f output P :=
    Measurable output ∧
      (P : Measure _) {ω | p.ε < f (output ω) - ⨅ y, f y} ≤ ENNReal.ofReal p.δ
  allowedAlgorithm p A := ∃ η : ℕ → ℝ, (∀ t, 0 < η t) ∧ A = ScheduledSgd.method η p.x0

end LongTails.Setups.HeavyTailedPL
