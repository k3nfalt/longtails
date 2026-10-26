import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.UnconstrainedLipschitzJacobianMonotone

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L : ℝ
  D : ℝ
  ε : ℝ
  m : ℕ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E ⊕ (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 ≤ p.L ∧ 0 < p.D ∧ 0 < p.ε ∧ 1 ≤ p.m
  admissible p F O :=
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (F x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ F x)) ∧
    Differentiable ℝ F ∧
    (∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    ∃ xstar, F xstar = 0 ∧ ‖p.x0 - xstar‖ ≤ p.D
  successful p F output P := ∀ᵐ ω ∂(P : Measure _), ‖F (output ω)‖ ≤ p.ε

end LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
