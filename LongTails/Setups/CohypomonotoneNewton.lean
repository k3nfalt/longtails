import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped RealInnerProductSpace

namespace LongTails.Setups.CohypomonotoneNewton

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  H : ℝ
  ρ : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.H ∧ 0 ≤ p.ρ ∧ 0 < p.R ∧ 0 < p.ε
  admissible p F oracle :=
    ∃ J : p.E → p.E →L[ℝ] p.E,
      (∀ history seed x, oracle.answer history (0, x) seed = (F x, J x)) ∧
      (∀ x, HasFDerivAt F (J x) x) ∧
      (∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖) ∧
      (∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) ∧
      (∃ xstar, F xstar = 0 ∧ ‖p.x0 - xstar‖ ≤ p.R)
  successful p F output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖F (output ω)‖ ≤ p.ε

end LongTails.Setups.CohypomonotoneNewton
