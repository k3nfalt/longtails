import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LongTails.Template

open scoped RealInnerProductSpace

namespace LongTails.Setups.CohypomonotoneInclusion

open OracleTemplate

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  L : ℝ
  ρ : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE

structure Params extends Public where
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := (p.E → p.E) × (p.E → Set p.E)
  Query p := p.E ⊕ (ℝ × p.E)
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 ≤ q.ρ ∧ q.ρ * q.L < 1 ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q I oracle :=
    ∃ J : ℝ → q.E → q.E,
      (∀ k seed x, oracle.answer k (0, (Sum.inl x)) seed = I.1 x) ∧
      (∀ k seed γ z, oracle.answer k (0, (Sum.inr (γ, z))) seed = J γ z) ∧
      (∀ γ z, 0 < γ → γ⁻¹ • (z - J γ z) ∈ I.2 (J γ z)) ∧
      (∀ x y, ∀ a ∈ I.2 x, ∀ b ∈ I.2 y, 0 ≤ ⟪a - b, x - y⟫) ∧
      (∀ x y, ‖I.1 x - I.1 y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x y, ∀ a ∈ I.2 x, ∀ b ∈ I.2 y,
        -q.ρ * ‖(I.1 x + a) - (I.1 y + b)‖ ^ 2 ≤ ⟪(I.1 x + a) - (I.1 y + b), x - y⟫) ∧
      (∃ xstar, -I.1 xstar ∈ I.2 xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q I output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ∃ ξ ∈ I.2 (output ω), ‖I.1 (output ω) + ξ‖ ≤ q.ε

end LongTails.Setups.CohypomonotoneInclusion
