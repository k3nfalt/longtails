import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone

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
  H₀ : ℝ
  ε : ℝ

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
  valid p := 0 < p.L ∧ 0 < p.D ∧ 0 ≤ p.H₀ ∧ 0 < p.ε
  admissible p F O :=
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (F x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ F x)) ∧
    ContDiff ℝ 2 F ∧
    (∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    ‖fderiv ℝ F p.x0‖ ≤ p.H₀ ∧
    ∃ xstar, F xstar = 0 ∧ ‖p.x0 - xstar‖ ≤ p.D
  successful p F output P := ∀ᵐ ω ∂(P : Measure _), ‖F (output ω)‖ ≤ p.ε

end LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
