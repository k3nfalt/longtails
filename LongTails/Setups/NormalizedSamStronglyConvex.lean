import LongTails.Algorithms.NormalizedSam
import LongTails.Setups.SmoothAndConvex

open scoped RealInnerProductSpace

namespace LongTails.Setups.NormalizedSamStronglyConvex

structure Params extends LongTails.Setups.SmoothAndConvex.Public where
  μ : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance p := (p.E → ℝ) × p.E
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p I oracle :=
    (∀ x, HasGradientAt I.1 (gradient I.1 x) x) ∧
    (∀ x y, ‖gradient I.1 x - gradient I.1 y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, I.1 x + ⟪gradient I.1 x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ I.1 y) ∧
    IsMinOn I.1 Set.univ I.2 ∧ I.1 p.x0 - I.1 I.2 ≤ p.Δ ∧
    (∀ k x seed, oracle.answer k (0, x) seed = gradient I.1 x)
  successful p I output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), I.1 (output ω) - I.1 I.2 ≤ p.ε
  allowedAlgorithm p A :=
    ∃ η : ℝ, 0 < η ∧ A = LongTails.Algorithms.NormalizedSam.method η p.ρ p.x0

end LongTails.Setups.NormalizedSamStronglyConvex
