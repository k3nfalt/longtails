import LongTails.Setups.SmoothAndConvex
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace LongTails.Setups.HessianLipschitzTemporalDiscrepancy

open OracleTemplate

structure Params extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  [finiteE : FiniteDimensional ℝ E]
  μ : ℝ
  M : ℝ
  D : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.finiteE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.M ∧ 0 ≤ p.D ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 2 f ∧
    (∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.M * ‖x - y‖) ∧
    (∃ e : ℕ → p.E,
      (∀ k x seed, O.answer k (0, x) seed = gradient f x + e k) ∧
      ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ p.D) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ f p.x0 - f xstar ≤ p.Δ)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.HessianLipschitzTemporalDiscrepancy
