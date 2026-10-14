import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.Floor.Ring
import LongTails.Algorithms.CyclicGradient

namespace LongTails.Setups.InterpolatedFiniteSum

open OracleTemplate OracleTemplate.CyclicInterpolation

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  m : ℕ
  [nonzero : NeZero m]
  L : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE Public.nonzero

structure Params extends Public where
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Fin p.m → p.E → ℝ
  Query p := Fin p.m × p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
    (∀ k seed i x, HasGradientAt (f i) (oracle.answer k (0, (i, x)) seed) x) ∧
    (∀ k seed i x y, ‖oracle.answer k (0, (i, x)) seed - oracle.answer k (0, (i, y)) seed‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, (∀ i, IsMinOn (f i) Set.univ xstar) ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q f output P :=
    ∃ xstar, (∀ i, IsMinOn (f i) Set.univ xstar) ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        (q.m : ℝ)⁻¹ * ∑ i, (f i (output ω) - f i xstar) ≤ q.ε
  allowedAlgorithm p algorithm := algorithm = cyclicGradient p.m p.L p.x0

end LongTails.Setups.InterpolatedFiniteSum
