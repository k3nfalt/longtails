import LongTails.Setups.SmoothAndConvex

open scoped RealInnerProductSpace

namespace LongTails.Setups.QuasarSignedBias

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  M : ℝ
  B : ℝ
  R : ℝ
  τ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := ℝ × p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.M ∧ 0 ≤ p.B ∧ 0 ≤ p.R ∧ 0 < p.τ ∧ p.τ ≤ 1 ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x, ‖gradient f x‖ ≤ p.M) ∧
    (∃ b : ℕ → p.E, b 0 = 0 ∧ (∀ k, ‖b k‖ ≤ p.B) ∧
      ∀ k x seed, O.answer k (0, x) seed = (f x, gradient f x + b (k.length + 1) - b k.length)) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R ∧
      ∀ x, p.τ * (f x - f xstar) ≤ ⟪gradient f x, x - xstar⟫)
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.QuasarSignedBias
