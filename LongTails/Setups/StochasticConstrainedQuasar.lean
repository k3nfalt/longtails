import LongTails.Setups.SmoothAndConvex
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticConstrainedQuasar

open OracleTemplate

structure Params extends SmoothAndConvex.Public.{0} where
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  D : ℝ
  γ : ℝ
  σ : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Params.finiteE Params.measurableE Params.borelE
  Params.countableE Params.measurableΩ

structure Instance (q : Params) where
  f : q.E → ℝ
  X : Set q.E
  xstar : q.E

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance := Instance
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L ∧ 0 < q.D ∧ 0 < q.γ ∧ q.γ ≤ 1 ∧ 0 ≤ q.σ ∧
    0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)) (proj : q.E → q.E),
    StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (i, x) seed => if i = 0 then g x seed else proj x } ∧
    (∀ z, proj z ∈ I.X ∧ ∀ w ∈ I.X, ⟪z - proj z, w - proj z⟫ ≤ 0) ∧
    IsCompact I.X ∧ Convex ℝ I.X ∧ q.x0 ∈ I.X ∧ I.xstar ∈ I.X ∧
    (∀ x ∈ I.X, ∀ y ∈ I.X, ‖x - y‖ ≤ q.D) ∧
    (∀ x ∈ I.X, HasGradientAt I.f (gradient I.f x) x) ∧
    (∀ x ∈ I.X, ∀ y ∈ I.X, ‖gradient I.f x - gradient I.f y‖ ≤ q.L * ‖x - y‖) ∧
    IsMinOn I.f I.X I.xstar ∧
    (∀ x ∈ I.X, q.γ * (I.f x - I.f I.xstar) ≤ ⟪gradient I.f x, x - I.xstar⟫) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x ∈ I.X, Integrable (g x) (p : Measure _)) ∧
    (∀ x ∈ I.X, (∫ ω, g x ω ∂(p : Measure _)) = gradient I.f x) ∧
    (∀ x ∈ I.X, Integrable (fun ω => ‖g x ω - gradient I.f x‖ ^ 2) (p : Measure _)) ∧
    (∀ x ∈ I.X, (∫ ω, ‖g x ω - gradient I.f x‖ ^ 2 ∂(p : Measure _)) ≤ q.σ ^ 2)
  successful q I output P :=
    Measurable output ∧
      (P : Measure _) {ω | ¬(output ω ∈ I.X ∧ I.f (output ω) - I.f I.xstar ≤ q.ε)} ≤
        ENNReal.ofReal q.δ

end LongTails.Setups.StochasticConstrainedQuasar
