import LongTails.Setups.GeneralizedSmoothAndConvex

open Set

namespace LongTails.Setups.RelativeGeneralizedSmoothConvex

open OracleTemplate

structure Public extends GeneralizedSmoothAndConvex.Public where
  α : ℝ
  ε : ℝ

structure Instance (p : Public) where
  f : p.E → ℝ
  grad : p.E → p.E

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 < p.R ∧ 0 < p.Δ ∧
    0 ≤ p.α ∧ p.α ≤ 1 / 100 ∧ 0 < p.ε
  admissible p I oracle :=
    (∀ history seed x, ‖oracle.answer history (0, x) seed - I.grad x‖ ≤ p.α * ‖I.grad x‖) ∧
    ConvexOn ℝ univ I.f ∧
    (∀ x, HasGradientAt I.f (I.grad x) x) ∧
    Continuous I.grad ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.grad (x + θ • (y - x))‖ ≤ M) →
      ‖I.grad x - I.grad y‖ ≤ (p.L0 + p.L1 * M) * ‖x - y‖) ∧
    (∃ xstar, IsMinOn I.f univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R ∧
      I.f p.x0 - I.f xstar ≤ p.Δ)
  successful p I output P :=
    ∃ xstar, IsMinOn I.f univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), I.f (output ω) - I.f xstar ≤ p.ε

end LongTails.Setups.RelativeGeneralizedSmoothConvex
