import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import LongTails.Template

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.DouglasRachfordSmoothConvex

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  γ : ℝ
  lam : ℝ
  w1 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

structure Params extends Public where
  L : ℝ
  R : ℝ
  ε : ℝ

inductive Query (p : Public) where
  | proxF (w : p.E)
  | proxG (v : p.E)

structure Instance (p : Public) where
  f : p.E → ℝ
  g : p.E → ℝ
  C : Set p.E

noncomputable def objective {p : Public} (I : Instance p) (x : p.E) : ℝ := I.f x + I.g x

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query := Query
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 < q.γ ∧ 0 < q.lam ∧ q.lam ≤ 1 ∧ 4 * q.γ * q.L ≤ q.lam ∧ 0 < q.R ∧ 0 < q.ε
  admissible q I oracle :=
    (∀ x, HasGradientAt I.f (gradient I.f x) x) ∧
    (∀ x y, I.f x + ⟪gradient I.f x, y - x⟫ ≤ I.f y) ∧
    (∀ x y, I.f y ≤ I.f x + ⟪gradient I.f x, y - x⟫ + q.L / 2 * ‖y - x‖ ^ 2) ∧
    Convex ℝ I.C ∧
    ConvexOn ℝ I.C I.g ∧
    (∀ k seed w, IsMinOn (fun x => I.f x + ‖x - w‖ ^ 2 / (2 * q.γ)) univ
      (oracle.answer k (0, (.proxF w)) seed)) ∧
    (∀ k seed v, oracle.answer k (0, (.proxG v)) seed ∈ I.C ∧
      IsMinOn (fun y => I.g y + ‖y - v‖ ^ 2 / (2 * q.γ)) I.C (oracle.answer k (0, (.proxG v)) seed)) ∧
    (∃ xstar ∈ I.C, IsMinOn (objective I) I.C xstar ∧
      ‖q.w1 - (xstar + q.γ • gradient I.f xstar)‖ ≤ q.R)
  successful q I output P :=
    ∃ xstar ∈ I.C, IsMinOn (objective I) I.C xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        output ω ∈ I.C ∧ objective I (output ω) - objective I xstar ≤ q.ε

end LongTails.Setups.DouglasRachfordSmoothConvex
