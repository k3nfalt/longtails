import LongTails.Setups.SmoothAndConvex

namespace LongTails.Setups.SmoothPL

open OracleTemplate

structure Params extends LongTails.Setups.SmoothAndConvex.Public where
  μ : ℝ
  Δ : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := LongTails.Setups.SmoothAndConvex.Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ ∧
      ∀ x, 2 * p.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.SmoothPL
