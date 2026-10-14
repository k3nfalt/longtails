import LongTails.Setups.ZerothOrderSmoothAndConvex

namespace LongTails.Setups.AffineDriftPL

open OracleTemplate

open LongTails.Setups.ZerothOrderSmoothAndConvex

structure Public where
  d : ℕ
  L : ℝ
  μ : ℝ
  ε : ℝ
  x0 : Point d

structure Params extends Public where
  Δ : ℝ
  ν : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Point p.d → ℝ
  Query p := Point p.d
  Reply _ := ℝ
  Output p := Point p.d
  publicInput := Params.toPublic
  valid p := 0 < p.d ∧ 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.ν ∧ 0 < p.ε ∧
    4 * (p.d : ℝ) * p.L * p.ν ≤ p.μ * p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ (a b : ℕ → ℝ) (e : ℕ → Point p.d → ℝ), (∀ k x, |e k x| ≤ p.ν) ∧
      ∀ k x seed, O.answer k (0, x) seed = f x + a (k / (p.d + 2)) +
        b (k / (p.d + 2)) * (k % (p.d + 2) : ℕ) + e k x) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ ∧
      ∀ x, 2 * p.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.AffineDriftPL
