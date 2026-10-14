import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import LongTails.Template

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.SlidingGeneralizedSmooth

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  L0 : ℝ
  L1 : ℝ
  M : ℝ
  R : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

abbrev Query (p : Public) := Fin 3 × p.E

@[simp] def Query.gradient {p : Public} (x : p.E) : Query p := (0, x)
@[simp] def Query.subgradient {p : Public} (x : p.E) : Query p := (1, x)
@[simp] def Query.project {p : Public} (x : p.E) : Query p := (2, x)

structure Instance (p : Public) where
  f : p.E → ℝ
  h : p.E → ℝ
  Q : Set p.E
  grad : p.E → p.E

noncomputable def objective {p : Public} (I : Instance p) (x : p.E) : ℝ := I.f x + I.h x

abbrev spec : Setup where
  numOracles := 3
  Params := Public
  Public := Public
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 ≤ q.M ∧ 0 < q.R ∧ 0 < q.Δ ∧ 0 ≤ q.G ∧ 0 < q.ε
  admissible q I oracle :=
    (∀ k seed x, oracle.answer k (Query.gradient x) seed = I.grad x) ∧
    (∀ k seed u, u ∈ I.Q → ‖oracle.answer k (Query.subgradient u) seed‖ ≤ q.M ∧
      ∀ v ∈ I.Q, I.h u + ⟪oracle.answer k (Query.subgradient u) seed, v - u⟫ ≤ I.h v) ∧
    (∀ k seed w, oracle.answer k (Query.project w) seed ∈ I.Q ∧
      ∀ u ∈ I.Q, ‖w - oracle.answer k (Query.project w) seed‖ ≤ ‖w - u‖) ∧
    ConvexOn ℝ univ I.f ∧
    (∀ x, HasGradientAt I.f (I.grad x) x) ∧
    Continuous I.grad ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.grad (x + θ • (y - x))‖ ≤ M) →
      ‖I.grad x - I.grad y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    Convex ℝ I.Q ∧
    q.x0 ∈ I.Q ∧
    (∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      objective I q.x0 - objective I xstar ≤ q.Δ ∧ ‖I.grad xstar‖ ≤ q.G)
  successful q I output P :=
    ∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        output ω ∈ I.Q ∧ objective I (output ω) - objective I xstar ≤ q.ε

end LongTails.Setups.SlidingGeneralizedSmooth
