import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace LongTails.Setups.LipschitzJacobianMonotone

open OracleTemplate MeasureTheory

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  X : Set E
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
  valid p := 0 < p.L ∧ 0 < p.D ∧ 0 < p.ε ∧ 1 ≤ p.m ∧
    IsCompact p.X ∧ Convex ℝ p.X ∧ p.x0 ∈ p.X ∧
    ∀ x ∈ p.X, ∀ y ∈ p.X, ‖x - y‖ ≤ p.D
  admissible p F O :=
    (∀ x ∈ p.X, DifferentiableAt ℝ F x) ∧
    (∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    (∀ x ∈ p.X, ∀ y ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (F x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ F x))
  successful p F output P := ∀ᵐ ω ∂(P : Measure _), output ω ∈ p.X ∧
    ∃ n : p.E, (∀ z ∈ p.X, ⟪n, z - output ω⟫ ≤ 0) ∧ ‖F (output ω) + n‖ ≤ p.ε

end LongTails.Setups.LipschitzJacobianMonotone
