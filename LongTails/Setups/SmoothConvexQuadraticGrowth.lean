import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import LongTails.Template

namespace LongTails.Setups.SmoothConvexQuadraticGrowth

open OracleTemplate

noncomputable def gradientMethod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℕ → ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E
  initial _ := (0, x0)
  query s := (0, s.2)
  update s reply := (s.1 + 1, s.2 - η s.1 • reply)
  output s := s.2

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  L : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

structure Params extends Public where
  μ : ℝ
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
  valid q := 0 < q.L ∧ 0 < q.μ ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f oracle :=
    ConvexOn ℝ Set.univ f ∧
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ k seed x y, ‖oracle.answer k (0, x) seed - oracle.answer k (0, y) seed‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    (∀ x, ∃ z, IsMinOn f Set.univ z ∧ q.μ / 2 * ‖x - z‖ ^ 2 ≤ f x - f z)
  successful q f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ q.ε
  allowedAlgorithm p algorithm :=
    ∃ η : ℕ → ℝ, (∀ t, 0 < η t) ∧ algorithm = gradientMethod η p.x0

end LongTails.Setups.SmoothConvexQuadraticGrowth
