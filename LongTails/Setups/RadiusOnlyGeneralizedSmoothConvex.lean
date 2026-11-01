import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import LongTails.Template

namespace LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  L0 : ℝ
  L1 : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

structure Params extends Public where
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L0 ∧ 0 < q.L1 ∧ 0 < q.R ∧ 0 < q.ε
  admissible q f oracle :=
    ConvexOn ℝ Set.univ f ∧
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ k seed, Differentiable ℝ (fun x => oracle.answer k (0, x) seed)) ∧
    (∀ k seed x, ‖fderiv ℝ (fun y => oracle.answer k (0, y) seed) x‖ ≤
      q.L0 + q.L1 * ‖oracle.answer k (0, x) seed‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ q.ε

end LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex
