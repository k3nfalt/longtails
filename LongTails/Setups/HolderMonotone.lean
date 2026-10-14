import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LongTails.Template

open scoped RealInnerProductSpace

namespace LongTails.Setups.HolderMonotone

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  r0 : ℝ
  ε : ℝ

attribute [instance] Public.normedE Public.linearE Public.finiteE

structure Params extends Public where
  L : ℝ
  H : ℝ
  α : ℝ
  R : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 ≤ q.L ∧ 0 ≤ q.H ∧ 0 < q.α ∧ q.α ≤ 1 ∧ 0 < q.r0 ∧ q.r0 ≤ q.R ∧ 0 < q.ε
  admissible q F oracle :=
    (∀ k seed x, oracle.answer k (0, x) seed = F x) ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    (∀ x y, ‖F x - F y‖ ≤ q.L * ‖x - y‖ + q.H * ‖x - y‖ ^ q.α) ∧
    (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q F output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖F (output ω)‖ ≤ q.ε

end LongTails.Setups.HolderMonotone
