import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace LongTails.Setups.InexactJacobianMonotone

open OracleTemplate MeasureTheory

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  M : ℝ
  δ : ℝ
  R : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.M ∧ 0 ≤ p.δ ∧ 0 < p.R ∧ 0 < p.ε
  admissible p F O :=
    (∀ x, DifferentiableAt ℝ F x) ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    (∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.M * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ ‖p.x0 - xstar‖ ≤ p.R) ∧
    (∀ history x seed, (O.answer history (0, x) seed).1 = F x ∧
      ‖(O.answer history (0, x) seed).2 - fderiv ℝ F x‖ ≤ p.δ)
  successful p F output P :=
    ∀ᵐ ω ∂(P : Measure _), ‖F (output ω)‖ ≤ p.ε

end LongTails.Setups.InexactJacobianMonotone
