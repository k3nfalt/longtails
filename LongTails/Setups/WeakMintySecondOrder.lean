import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped RealInnerProductSpace

namespace LongTails.Setups.WeakMintySecondOrder

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L₁ : ℝ
  L₂ : ℝ
  ρ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE

structure Params extends Public where
  R : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E ⊕ p.E
  Reply p := p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L₁ ∧ 0 < q.L₂ ∧ 0 ≤ q.ρ ∧ q.ρ * q.L₁ < 2 ∧
    0 ≤ q.R ∧ 0 < q.ε
  admissible q F oracle :=
    ∃ J : q.E → q.E →L[ℝ] q.E,
      (∀ k seed x, oracle.answer k (0, Sum.inl x) seed = (F x, 0)) ∧
      (∀ k seed x, oracle.answer k (0, Sum.inr x) seed = (0, J x)) ∧
      (∀ x, HasFDerivAt F (J x) x) ∧
      (∀ x y, ‖J x - J y‖ ≤ q.L₂ * ‖x - y‖) ∧
      (∀ x y, ‖F x - F y‖ ≤ q.L₁ * ‖x - y‖) ∧
      (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
        ∀ x, -(q.ρ / 2) * ‖F x‖ ^ 2 ≤ ⟪F x, x - xstar⟫)
  successful q F output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖F (output ω)‖ ≤ q.ε

end LongTails.Setups.WeakMintySecondOrder
