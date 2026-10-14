import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LongTails.Template

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.ConstrainedGeneralizedMonotone

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  L0 : ℝ
  L1 : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE

structure Params extends Public where
  R : ℝ
  G : ℝ
  G0 : ℝ
  ε : ℝ

structure Instance (p : Public) where
  F : p.E → p.E
  X : Set p.E

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Public
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 ≤ q.G ∧ 0 ≤ q.G0 ∧ 0 < q.ε
  admissible q I oracle :=
    (∀ k seed x, oracle.answer k (0, x) seed = I.F x) ∧
    (∃ P : q.E → q.E, (∀ k seed z, oracle.answer k (1, z) seed = P z) ∧
      ∀ z, P z ∈ I.X ∧ ∀ w ∈ I.X, ⟪z - P z, w - P z⟫ ≤ 0) ∧
    Convex ℝ I.X ∧
    Continuous I.F ∧
    (∀ x y, 0 ≤ ⟪I.F x - I.F y, x - y⟫) ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.F (x + θ • (y - x))‖ ≤ M) →
      ‖I.F x - I.F y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    q.x0 ∈ I.X ∧
    ‖I.F q.x0‖ ≤ q.G0 ∧
    (∃ xstar ∈ I.X, (∀ w ∈ I.X, 0 ≤ ⟪I.F xstar, w - xstar⟫) ∧
      ‖q.x0 - xstar‖ ≤ q.R ∧ ‖I.F xstar‖ ≤ q.G)
  successful q I output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), output ω ∈ I.X ∧
      ∃ ξ : q.E, (∀ w ∈ I.X, ⟪ξ, w - output ω⟫ ≤ 0) ∧ ‖I.F (output ω) + ξ‖ ≤ q.ε

end LongTails.Setups.ConstrainedGeneralizedMonotone
