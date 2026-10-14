import LongTails.Setups.StochasticGeneralizedMonotone

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticCohypomonotoneInclusion

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  ρ : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE Params.borelE
  Params.measurableΩ

def reply {E Ω : Type} (g : E → Ω → E) (J : ℝ → E → E) (q : E ⊕ (ℝ × E)) (ω : Ω) : E :=
  Sum.elim (fun x => g x ω) (fun γz => J γz.1 γz.2) q

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := (p.E → p.E) × (p.E → Set p.E)
  Query p := p.E ⊕ (ℝ × p.E)
  Reply p := p.E
  Output p := p.E × p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.ρ ∧ 2 * q.ρ * q.L < 1 ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (J : ℝ → q.E → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ q => reply g J q.2 } ∧
      (∀ γ z, 0 < γ → γ⁻¹ • (z - J γ z) ∈ I.2 (J γ z)) ∧
      (∀ x y, ∀ a ∈ I.2 x, ∀ b ∈ I.2 y, 0 ≤ ⟪a - b, x - y⟫) ∧
      (∀ x y, ‖I.1 x - I.1 y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x y, ∀ a ∈ I.2 x, ∀ b ∈ I.2 y,
        -q.ρ * ‖(I.1 x + a) - (I.1 y + b)‖ ^ 2 ≤ ⟪(I.1 x + a) - (I.1 y + b), x - y⟫) ∧
      (∃ xstar, -I.1 xstar ∈ I.2 xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
      LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure _) I.1 g q.σ
  successful q I output P :=
    Measurable output ∧ (∀ ω, (output ω).2 ∈ I.2 (output ω).1) ∧
      Integrable (fun ω => ‖I.1 (output ω).1 + (output ω).2‖) (P : Measure _) ∧
      ∫ ω, ‖I.1 (output ω).1 + (output ω).2‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticCohypomonotoneInclusion
