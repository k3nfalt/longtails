import LongTails.Setups.SmoothAndConvex

open scoped RealInnerProductSpace

namespace LongTails.Setups.UncalibratedSharp

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  μ : ℝ
  ρ : ℝ
  α : ℝ
  β : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE

structure Params extends Public where
  G : ℝ
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := ℝ × p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 ≤ p.ρ ∧ p.ρ < p.μ ∧ p.μ ≤ p.G ∧ 0 < p.α ∧ p.α ≤ p.β ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p f O :=
    (∀ x y, |f x - f y| ≤ p.G * ‖x - y‖) ∧
    ∃ u, IsMinOn f Set.univ u ∧ ‖p.x0 - u‖ ≤ p.R ∧
      (∀ x, p.μ * ‖x - u‖ ≤ f x - f u) ∧
      ∀ k x seed, ∃ (γ r : ℝ) (g e : p.E), 0 < γ ∧ ‖g‖ ≤ p.G ∧ ‖e‖ ≤ p.ρ ∧
        (∀ y, f x + ⟪g, y - x⟫ ≤ f y) ∧
        p.α * (f x - f u) ≤ r ∧ r ≤ p.β * (f x - f u) ∧
        O.answer k (0, x) seed = (γ * r, γ • (g + e))
  successful p f output P :=
    ∃ u, IsMinOn f Set.univ u ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f u ≤ p.ε

end LongTails.Setups.UncalibratedSharp
