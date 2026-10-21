import LongTails.Setups.SmoothPL

namespace LongTails.Setups.RelativeDiscrepancyPL

open OracleTemplate

structure Public extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  D : ℝ

structure Params extends Public where
  μ : ℝ
  Δ : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.D ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ g : ℕ → p.E → p.E,
      (∀ k x seed, O.answer k (0, x) seed = g k.length x) ∧
      ∀ start n x, ‖∑ i : Fin n, (g (start + i.val) x - gradient f x)‖ ≤
        p.D * ‖gradient f x‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ ∧
      ∀ x, 2 * p.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.RelativeDiscrepancyPL
