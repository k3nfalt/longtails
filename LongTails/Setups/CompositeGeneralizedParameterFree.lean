import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import LongTails.Template

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.CompositeGeneralizedParameterFree

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  x0 : E
  h0 : ℝ

attribute [instance] Public.normedE Public.linearE Public.completeE

structure Params extends Public where
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ

inductive Query (p : Public) where
  | gradient (x : p.E)
  | prox (a : ℝ) (z v : p.E)

structure Instance (p : Public) where
  f : p.E → ℝ
  ψ : p.E → ℝ
  Q : Set p.E
  grad : p.E → p.E
  prox : ℝ → p.E → p.E → p.E

noncomputable def objective {p : Public} (I : Instance p) (x : p.E) : ℝ := I.f x + I.ψ x

noncomputable def proxObjective {p : Public} (I : Instance p) (a : ℝ) (z v u : p.E) : ℝ :=
  ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + I.ψ u

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query := Query
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.h0 ∧ 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 < q.Δ ∧ 0 ≤ q.G ∧ 0 < q.ε
  admissible q I oracle :=
    (∀ k seed x, oracle.answer k (0, (.gradient x)) seed = I.grad x) ∧
    (∀ k seed a z v, oracle.answer k (0, (.prox a z v)) seed = I.prox a z v) ∧
    ConvexOn ℝ univ I.f ∧
    (∀ x, HasGradientAt I.f (I.grad x) x) ∧
    Continuous I.grad ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.grad (x + θ • (y - x))‖ ≤ M) →
      ‖I.grad x - I.grad y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    Convex ℝ I.Q ∧
    ConvexOn ℝ I.Q I.ψ ∧
    (∀ a, 0 < a → ∀ z v, I.prox a z v ∈ I.Q ∧
      IsMinOn (proxObjective I a z v) I.Q (I.prox a z v)) ∧
    q.x0 ∈ I.Q ∧
    (∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      objective I q.x0 - objective I xstar ≤ q.Δ ∧ ‖I.grad xstar‖ ≤ q.G)
  successful q I output P :=
    ∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        output ω ∈ I.Q ∧ objective I (output ω) - objective I xstar ≤ q.ε

end LongTails.Setups.CompositeGeneralizedParameterFree
