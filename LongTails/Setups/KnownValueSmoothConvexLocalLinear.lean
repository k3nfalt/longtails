import LongTails.Algorithms.SplitBrox
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.KnownValueSmoothConvexLocalLinear

open OracleTemplate OracleTemplate.SplitBrox

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  L : ℝ
  R : ℝ
  ε : ℝ
  fstar : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

structure Instance (p : Public) where
  f : p.E → ℝ
  C : Set p.E

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := Instance
  Query p := Query p.E
  Reply p := Reply p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p I O :=
    Convex ℝ I.C ∧ IsClosed I.C ∧ p.x0 ∈ I.C ∧
    (∀ x ∈ I.C, HasGradientAt I.f (gradient I.f x) x) ∧
    (∀ x ∈ I.C, ∀ y ∈ I.C, I.f x + ⟪gradient I.f x, y - x⟫ ≤ I.f y) ∧
    (∀ x ∈ I.C, ∀ y ∈ I.C,
      I.f y ≤ I.f x + ⟪gradient I.f x, y - x⟫ + p.L / 2 * ‖y - x‖ ^ 2) ∧
    (∀ k seed x, x ∈ I.C → O.answer k (0, .inl x) seed =
      .inl (I.f x, gradient I.f x)) ∧
    (∀ k seed x r g, x ∈ I.C → 0 ≤ r →
      ∃ v ∈ I.C, ‖v - x‖ ≤ r ∧
        (∀ z ∈ I.C, ‖z - x‖ ≤ r → ⟪g, v⟫ ≤ ⟪g, z⟫) ∧
        O.answer k (0, .inr (x, r, g)) seed = .inr v) ∧
    (∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧ I.f xstar = p.fstar ∧
      ‖p.x0 - xstar‖ ≤ p.R)
  successful p I output P :=
    ∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧ I.f xstar = p.fstar ∧
      ∀ᵐ ω ∂(P : Measure _), output ω ∈ I.C ∧ I.f (output ω) - I.f xstar ≤ p.ε

end LongTails.Setups.KnownValueSmoothConvexLocalLinear
