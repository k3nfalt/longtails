import LongTails.Setups.UscgConstant

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.ScgConstant

open OracleTemplate
open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  N : Seminorm ℝ (Space d)
  lmo : Space d → Space d
  ρ : ℝ
  D₂ : ℝ
  x₁ : Space d
  L : ℝ
  L₂ : ℝ
  σ : ℝ
  Δ : ℝ
  α : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

noncomputable def horizon (p : Params) : ℕ :=
  ⌈((p.Δ + 2 * p.L * p.ρ ^ 2 + (2 * p.L₂ * p.D₂ ^ 2 + 4 * p.D₂ * p.σ) / p.α) / p.ε) ^ 2⌉₊

noncomputable def stepSize (p : Params) : ℝ := 1 / Real.sqrt (horizon p + 1)

noncomputable def method (p : Params) : Algorithm (Space p.d) (Space p.d) (Space p.d) :=
  scg p.lmo (constantMomentum p.α) (stepSize p) (horizon p) p.x₁

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p.d → ℝ
  Query p := Space p.d
  Reply p := Space p.d
  Output p := Space p.d
  publicInput p := p
  valid p :=
    (∀ x, p.N x = 0 → x = 0) ∧ 0 < p.ρ ∧ IsBallLMO p.N p.ρ p.lmo ∧
      (∀ x y, p.N x ≤ p.ρ → p.N y ≤ p.ρ → ‖x - y‖ ≤ p.D₂) ∧ p.N p.x₁ ≤ p.ρ ∧
      0 < p.L ∧ 0 ≤ p.L₂ ∧ 0 ≤ p.σ ∧ 0 ≤ p.Δ ∧ 0 < p.α ∧ p.α < 1 ∧ 0 < p.ε
  admissible p f O :=
    ∃ (g : Space p.d → p.Ω → Space p.d) (P₀ : ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (ℕ → p.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → p.Ω) => ξ k) (P₀ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      ConstrainedProblem p.N p.ρ p.L p.L₂ p.σ p.Δ p.x₁ f g (P₀ : Measure _)
  successful p f output P :=
    Measurable output ∧ (∀ ω, p.N (output ω) ≤ p.ρ) ∧ ∀ u, p.N u ≤ p.ρ →
      Integrable (fun ω => ⟪gradient f (output ω), output ω - u⟫) (P : Measure _) ∧
      ∫ ω, ⟪gradient f (output ω), output ω - u⟫ ∂(P : Measure _) ≤
        p.ε + p.D₂ * Real.sqrt (2 * p.α) * p.σ
  allowedAlgorithm p A := A = method p

attribute [local simp] horizon stepSize method

end LongTails.Setups.ScgConstant
