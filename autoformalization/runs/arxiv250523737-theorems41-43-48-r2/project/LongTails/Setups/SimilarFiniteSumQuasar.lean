import LongTails.Setups.SmoothAndConvex
import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped RealInnerProductSpace

namespace LongTails.Setups.SimilarFiniteSumQuasar

open OracleTemplate

structure Params extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  n : ℕ
  [nonzero : NeZero n]
  μ : ℝ
  γ : ℝ
  δ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.γ ∧ p.γ ≤ 1 ∧ 0 ≤ p.δ ∧
    384 * p.δ ^ 2 ≤ p.γ ^ 3 * p.μ ^ 2 ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ k i x seed, O.answer k (0, (i, x)) seed = gradient (f i) x) ∧
    (∀ x y, ‖gradient F x - gradient F y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ i x y, ‖(gradient (f i) x - gradient F x) -
      (gradient (f i) y - gradient F y)‖ ≤ p.δ * ‖x - y‖) ∧
    (∀ x y, F x + ⟪gradient F x, y - x⟫ -
      p.γ * p.μ / (2 * Real.sqrt (p.μ / p.L)) * ‖y - x‖ ^ 2 ≤ F y) ∧
    (∃ xstar, IsMinOn F Set.univ xstar ∧ F p.x0 - F xstar ≤ p.Δ ∧
      (∀ x, p.γ * F x + ⟪gradient F x, xstar - x⟫ +
        p.γ * p.μ / 2 * ‖xstar - x‖ ^ 2 ≤ p.γ * F xstar) ∧
      ∀ x, p.γ * p.μ / (2 * (2 - p.γ)) * ‖x - xstar‖ ^ 2 ≤ F x - F xstar)
  successful p f output P :=
    ∃ xstar, IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (output ω) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤ p.ε

end LongTails.Setups.SimilarFiniteSumQuasar
