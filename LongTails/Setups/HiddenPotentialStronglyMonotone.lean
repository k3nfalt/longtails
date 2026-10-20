import LongTails.Setups.SmoothAndConvex

open scoped RealInnerProductSpace

namespace LongTails.Setups.HiddenPotentialStronglyMonotone

open OracleTemplate

structure Public extends LongTails.Setups.SmoothAndConvex.Public where
  μ : ℝ
  s : ℝ
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := p.E → p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := fun p => p
  valid p := 0 < p.μ ∧ 0 ≤ p.L ∧ 0 ≤ p.s ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p F oracle :=
    (∀ k seed x, oracle.answer k (0, x) seed = F x) ∧
    (∀ x y, p.μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) ∧
    (∃ φ : p.E → ℝ,
      (∀ x, HasGradientAt φ (gradient φ x) x) ∧
      (∀ x y, ‖gradient φ x - gradient φ y‖ ≤ p.L * ‖x - y‖) ∧
      (∀ x y, ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ p.s * ‖x - y‖)) ∧
    (∃ xstar, F xstar = 0 ∧ ‖p.x0 - xstar‖ ≤ p.R)
  successful p F output P :=
    ∃ xstar, F xstar = 0 ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ‖output ω - xstar‖ ≤ p.ε

end LongTails.Setups.HiddenPotentialStronglyMonotone
