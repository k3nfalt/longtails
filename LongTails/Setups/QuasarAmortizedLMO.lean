import LongTails.Setups.SmoothAndConvex

open scoped RealInnerProductSpace

namespace LongTails.Setups.QuasarAmortizedLMO

open OracleTemplate

structure Public extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public.{0} where
  τ : ℝ

structure Params extends Public where
  C : Set E
  D : ℝ
  Γ : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E ⊕ p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 ≤ p.L ∧ 0 < p.τ ∧ p.τ ≤ 1 ∧ 0 ≤ p.D ∧ 0 ≤ p.Γ ∧ 0 < p.ε ∧
    Convex ℝ p.C ∧ p.x0 ∈ p.C ∧ ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ k x seed, O.answer k (0, (Sum.inl x)) seed = gradient f x) ∧
    (∃ δ : ℕ → ℝ, (∀ k, 0 ≤ δ k) ∧ (∀ n, ∑ k ∈ Finset.range n, δ k ≤ p.Γ) ∧
      ∀ history, history.length % 2 = 1 → ∀ v seed, O.answer history (0, (Sum.inr v)) seed ∈ p.C ∧
        ∀ u ∈ p.C, ⟪v, O.answer history (0, (Sum.inr v)) seed⟫ ≤ ⟪v, u⟫ + δ (history.length / 2)) ∧
    (∃ xstar ∈ p.C, IsMinOn f p.C xstar ∧
      ∀ x ∈ p.C, p.τ * (f x - f xstar) ≤ ⟪gradient f x, x - xstar⟫)
  successful p f output P :=
    ∃ xstar ∈ p.C, IsMinOn f p.C xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), output ω ∈ p.C ∧ f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.QuasarAmortizedLMO
