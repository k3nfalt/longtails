import LongTails.Setups.StochasticSmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Metric

namespace LongTails.Setups.LocalHiddenConvexStochastic

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  R : ℝ
  σ : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE Public.completeE
  Public.measurableE Public.borelE Public.countableE Public.measurableΩ

structure Params extends Public where
  μ : ℝ
  LJ : ℝ
  ε : ℝ

structure Instance (p : Public) where
  F : p.E → ℝ
  H : p.E → ℝ
  c : p.E → p.E
  J : p.E → p.E →L[ℝ] p.E
  U : Set p.E

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 < q.R ∧ 0 ≤ q.σ ∧ 0 < q.μ ∧ 0 ≤ q.LJ ∧ 0 < q.ε ∧
    32 * q.LJ * q.R ≤ q.μ
  admissible q I O :=
    ∃ (oracle : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω),
    O = { Seed := fun _ => q.Ω
          law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)), inferInstance⟩
          answer := fun _ (_, x) seed => oracle x seed } ∧
    (∀ x ∈ ball q.x0 (3 * q.R), I.F x = I.H (I.c x)) ∧
    IsOpen I.U ∧ ConvexOn ℝ I.U I.H ∧ (∀ u ∈ I.U, DifferentiableAt ℝ I.H u) ∧
    (∀ x ∈ closedBall q.x0 (2 * q.R), I.c x ∈ I.U ∧ HasFDerivAt I.c (I.J x) x ∧
      ∀ v, q.μ * ‖v‖ ≤ ‖I.J x v‖) ∧
    (∀ x ∈ closedBall q.x0 (2 * q.R), ∀ y ∈ closedBall q.x0 (2 * q.R),
      ‖I.J x - I.J y‖ ≤ q.LJ * ‖x - y‖) ∧
    (∀ x, HasGradientAt I.F (gradient I.F x) x) ∧
    (∀ x y, ‖gradient I.F x - gradient I.F y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar ∈ closedBall q.x0 q.R, IsMinOn I.F Set.univ xstar) ∧
    LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient q.E q.Ω p I.F oracle q.σ
  successful q I output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn I.F Set.univ xstar ∧
      Integrable (fun ω => I.F (output ω) - I.F xstar) (P : Measure _) ∧
      (∫ ω, I.F (output ω) - I.F xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.LocalHiddenConvexStochastic
