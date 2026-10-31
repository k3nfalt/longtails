import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LongTails.Template

open scoped RealInnerProductSpace BigOperators
open MeasureTheory

namespace LongTails.Setups.FiniteSumWeakMintyInclusion

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  n : ℕ
  L : ℝ
  Λ : ℝ
  ρ : ℝ
  R : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE
  Params.measurableE Params.borelE

noncomputable def operator {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (F : Fin n → E → E) (x : E) : E :=
  (n : ℝ)⁻¹ • ∑ i, F i x

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := (Fin p.n → p.E → p.E) × (p.E → Set p.E)
  Query p := (Fin p.n × p.E) ⊕ (ℝ × p.E)
  Reply p := p.E
  Output p := p.E × p.E
  publicInput := fun p => p
  valid p := 0 < p.n ∧ 0 < p.L ∧ p.L ≤ p.Λ ∧ 0 ≤ p.ρ ∧
    p.ρ * p.L < 1 ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p I oracle :=
    ∃ J : ℝ → p.E → p.E,
      (∀ history seed i x, oracle.answer history (0, Sum.inl (i, x)) seed = I.1 i x) ∧
      (∀ history seed η z, oracle.answer history (0, Sum.inr (η, z)) seed = J η z) ∧
      (∀ η z, 0 < η → η⁻¹ • (z - J η z) ∈ I.2 (J η z)) ∧
      (∀ x y, ∀ a ∈ I.2 x, ∀ b ∈ I.2 y, 0 ≤ ⟪a - b, x - y⟫) ∧
      (∀ x y, ‖operator I.1 x - operator I.1 y‖ ≤ p.L * ‖x - y‖) ∧
      (∀ x y, (p.n : ℝ)⁻¹ * ∑ i, ‖I.1 i x - I.1 i y‖ ^ 2 ≤
        p.Λ ^ 2 * ‖x - y‖ ^ 2) ∧
      (∃ xstar, -operator I.1 xstar ∈ I.2 xstar ∧ ‖p.x0 - xstar‖ ≤ p.R ∧
        ∀ y, ∀ v ∈ I.2 y, -p.ρ * ‖operator I.1 y + v‖ ^ 2 ≤
          ⟪operator I.1 y + v, y - xstar⟫)
  successful p I output P :=
    Measurable output ∧
      (∀ᵐ ω ∂(P : Measure _), (output ω).2 ∈ I.2 (output ω).1) ∧
      Integrable (fun ω => ‖operator I.1 (output ω).1 + (output ω).2‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖operator I.1 (output ω).1 + (output ω).2‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.FiniteSumWeakMintyInclusion
