import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LongTails.Template

open scoped RealInnerProductSpace

namespace LongTails.Setups.RadiusGeneralizedLipschitzMonotone

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE

structure Params extends Public where
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q F oracle :=
    (∀ k seed x, oracle.answer k (0, x) seed = F x) ∧
    Continuous F ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    (∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q F output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖F (output ω)‖ ≤ q.ε

end LongTails.Setups.RadiusGeneralizedLipschitzMonotone
