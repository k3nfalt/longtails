import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import LongTails.Template

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.LipschitzCompositeGeneralizedSmooth

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  L0 : ℝ
  L1 : ℝ
  M : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

structure Params extends Public where
  R : ℝ
  ε : ℝ

inductive Query (p : Public) where
  | gradient (x : p.E)
  | prox (a : ℝ) (z v : p.E)
  | value (x : p.E)

inductive Reply (p : Public) where
  | vector (g : p.E)
  | scalar (r : ℝ)

structure Instance (p : Public) where
  f : p.E → ℝ
  ψ : p.E → ℝ
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
  Reply := Reply
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L0 ∧ 0 < q.L1 ∧ 0 ≤ q.M ∧ 0 < q.R ∧ 0 < q.ε
  admissible q I oracle :=
    (∀ k seed x, oracle.answer k (0, .gradient x) seed = .vector (I.grad x)) ∧
    (∀ k seed a z v, oracle.answer k (0, .prox a z v) seed = .vector (I.prox a z v)) ∧
    (∀ k seed x, oracle.answer k (0, .value x) seed = .scalar (I.ψ x)) ∧
    ConvexOn ℝ univ I.f ∧
    (∀ x, HasGradientAt I.f (I.grad x) x) ∧
    Continuous I.grad ∧
    (∀ x y S, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.grad (x + θ • (y - x))‖ ≤ S) →
      ‖I.grad x - I.grad y‖ ≤ (q.L0 + q.L1 * S) * ‖x - y‖) ∧
    ConvexOn ℝ univ I.ψ ∧
    (∀ x y, |I.ψ x - I.ψ y| ≤ q.M * ‖x - y‖) ∧
    (∀ a, 0 < a → ∀ z v, IsMinOn (proxObjective I a z v) univ (I.prox a z v)) ∧
    (∃ xstar, IsMinOn (objective I) univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q I output P :=
    ∃ xstar, IsMinOn (objective I) univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        objective I (output ω) - objective I xstar ≤ q.ε

end LongTails.Setups.LipschitzCompositeGeneralizedSmooth
