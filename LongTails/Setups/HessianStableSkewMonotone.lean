import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace LongTails.Setups.HessianStableSkewMonotone

open OracleTemplate MeasureTheory

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  M : ℝ
  D : ℝ
  ε : ℝ

attribute [instance] Public.normedE Public.innerE Public.finiteE

structure Params where
  pub : Public
  Λ : ℝ

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E ⊕ (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p.pub
  valid p := 0 < p.pub.M ∧ 0 < p.pub.D ∧ 0 < p.pub.ε ∧ 0 ≤ p.Λ
  admissible p F O :=
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (F x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ F x)) ∧
    Differentiable ℝ F ∧
    (∃ S : p.pub.E →L[ℝ] p.pub.E, (∀ v, ⟪S v, v⟫ = 0) ∧
      (∀ x u v, ⟪(fderiv ℝ F x - S) u, v⟫ = ⟪u, (fderiv ℝ F x - S) v⟫) ∧
      (∀ x v, 0 ≤ ⟪(fderiv ℝ F x - S) v, v⟫) ∧
      ∀ x y v, ⟪(fderiv ℝ F y - S) v, v⟫ ≤
        Real.exp (p.pub.M * ‖y - x‖) * ⟪(fderiv ℝ F x - S) v, v⟫) ∧
    ∃ xstar, F xstar = 0 ∧ ‖p.pub.x0 - xstar‖ ≤ p.pub.D ∧
      ∀ x, ‖x - xstar‖ ≤ 3 * p.pub.D + 1 / (4 * p.pub.M) → ‖fderiv ℝ F x‖ ≤ p.Λ
  successful p F output P := ∀ᵐ ω ∂(P : Measure _), ‖F (output ω)‖ ≤ p.pub.ε

end LongTails.Setups.HessianStableSkewMonotone
