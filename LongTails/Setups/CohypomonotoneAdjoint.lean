import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped RealInnerProductSpace

namespace LongTails.Setups.CohypomonotoneAdjoint

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L : ℝ
  L₂ : ℝ
  ρ : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.finiteE

structure Params extends Public where
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E ⊕ (p.E × p.E)
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 ≤ q.L₂ ∧ 0 ≤ q.ρ ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q F oracle :=
    ∃ J : q.E → q.E →L[ℝ] q.E,
      (∀ k seed x, oracle.answer k (0, (Sum.inl x)) seed = F x) ∧
      (∀ k seed x w h, ⟪oracle.answer k (0, (Sum.inr (x, w))) seed, h⟫ = ⟪w, J x h⟫) ∧
      (∀ x, HasFDerivAt F (J x) x) ∧
      (∀ x y, ‖J x - J y‖ ≤ q.L₂ * ‖x - y‖) ∧
      (∀ x y, ‖F x - F y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x y, -q.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) ∧
      (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q F output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖F (output ω)‖ ≤ q.ε

end LongTails.Setups.CohypomonotoneAdjoint
