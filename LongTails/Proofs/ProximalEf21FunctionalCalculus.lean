import LongTails.Proofs.ProximalEf21Geometry
import LongTails.Proofs.ProximalEf21MomentCalculus

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21FunctionalCalculus

open LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma signed_correction_change (ψ : E → ℝ) (x y xstar m mnext : E) :
    -(ψ y - ψ xstar + ⟪mnext, y - xstar⟫_ℝ) / 8 +
        (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8 =
      -(ψ y - ψ x) / 8 - ⟪mnext - m, y - xstar⟫_ℝ / 8 +
        ⟪m, x - y⟫_ℝ / 8 := by
  have hv : x - xstar = (x - y) + (y - xstar) := by abel
  rw [hv]
  simp only [inner_add_right, inner_sub_left]
  ring

lemma functional_change_from_model (F ψ : E → ℝ) {μ τ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (xstar x y m mnext z znext g : E)
    (hsmooth : F y - F x ≤ -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z ≤
      -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
        (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
        ⟪mnext - m, y - xstar⟫_ℝ / 8 + ⟪m, x - y⟫_ℝ / 8 +
        (-⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2) / (μ * τ) := by
  have hmodel := proximal_model_change ψ hτ x y m mnext z znext hsupport
  have hscaled := div_le_div_of_nonneg_right hmodel
    (show 0 ≤ μ * τ by positivity)
  have hsign := signed_correction_change ψ x y xstar m mnext
  unfold functionalEnergy
  have hsplit :
      (modelDecrease ψ τ y mnext znext - modelDecrease ψ τ x m z) / (μ * τ) =
        modelDecrease ψ τ y mnext znext / (μ * τ) -
          modelDecrease ψ τ x m z / (μ * τ) := by ring
  have hrhs :
      (ψ y - ψ x - ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
        ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2) / (μ * τ) =
      (ψ y - ψ x) / (μ * τ) +
        (-⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2) / (μ * τ) := by ring
  rw [hsplit, hrhs] at hscaled
  nlinarith only [hsmooth, hscaled, hsign]

noncomputable def componentBound (_F ψ : E → ℝ) (μ τ γ α : ℝ)
    (xstar x y m z g b : E) : ℝ :=
  -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
    (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
    (α / 8) * ⟪g - m + b, y - xstar⟫_ℝ + ⟪m, x - y⟫_ℝ / 8 -
    ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ / (μ * τ) +
    γ / τ * ⟪x - z, g - m + b⟫_ℝ +
    μ * γ ^ 2 / 2 * ‖g - m + b‖ ^ 2

lemma functional_change_with_noise (F ψ : E → ℝ) {μ τ γ α : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hα : α = μ * γ)
    (xstar x y m mnext z znext g b ζ : E)
    (hupdate : mnext = m + α • (g - m + b + ζ))
    (hsmooth : F y - F x ≤ -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z ≤
      componentBound F ψ μ τ γ α xstar x y m z g b +
        γ / τ * ⟪x - z, ζ⟫_ℝ - α / 8 * ⟪y - xstar, ζ⟫_ℝ +
        μ * γ ^ 2 * ⟪g - m + b, ζ⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ‖ ^ 2 := by
  have hbase := functional_change_from_model F ψ hμ hτ
    xstar x y m mnext z znext g hsmooth hsupport
  have hinc : mnext - m = α • (g - m + b + ζ) := by rw [hupdate]; abel
  rw [hinc, real_inner_smul_left, real_inner_smul_right, square_smul, square_add] at hbase
  rw [inner_add_left, inner_add_right] at hbase
  have hid :
      -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2 +
        (7 / 8 + 1 / (μ * τ)) * (ψ y - ψ x) -
        (α * (⟪g - m + b, y - xstar⟫_ℝ + ⟪ζ, y - xstar⟫_ℝ)) / 8 +
        ⟪m, x - y⟫_ℝ / 8 +
        (-⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          α * (⟪x - z, g - m + b⟫_ℝ + ⟪x - z, ζ⟫_ℝ) +
          τ / 2 * (α ^ 2 * (‖g - m + b‖ ^ 2 +
            2 * ⟪g - m + b, ζ⟫_ℝ + ‖ζ‖ ^ 2))) / (μ * τ) =
      componentBound F ψ μ τ γ α xstar x y m z g b +
        γ / τ * ⟪x - z, ζ⟫_ℝ - α / 8 * ⟪y - xstar, ζ⟫_ℝ +
        μ * γ ^ 2 * ⟪g - m + b, ζ⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ‖ ^ 2 := by
    unfold componentBound
    rw [hα]
    rw [real_inner_comm ζ (y - xstar)]
    field_simp [ne_of_gt hμ, ne_of_gt hτ]
    <;> ring
  calc
    functionalEnergy F ψ μ τ xstar y mnext znext -
        functionalEnergy F ψ μ τ xstar x m z ≤ _ := hbase
    _ = _ := hid

lemma componentBound_assembled (F ψ : E → ℝ) {μ τ γ α : ℝ}
    (hμ : μ ≠ 0) (hγ : γ ≠ 0) (hτ : τ ≠ 0)
    (xstar x y m v z g b : E) :
    componentBound F ψ μ τ γ α xstar x y m z g b =
      -(7 / (8 * γ) + μ / 2) * ‖y - x‖ ^ 2 -
      (7 / 8 + 1 / (μ * τ)) *
        (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) -
      α / 8 * ⟪y - xstar, g - m + b⟫_ℝ +
      7 / 8 * ⟪v - m, x - y⟫_ℝ + ⟪b, x - y⟫_ℝ -
      γ * ⟪g - m + b, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ -
      γ / (μ * τ) *
        ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
          γ⁻¹ • (x - y)⟫_ℝ +
      μ * γ ^ 2 / 2 * ‖g - m + b‖ ^ 2 := by
  unfold componentBound
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_neg_right, inner_neg_left, real_inner_comm]
  field_simp [hμ, hγ, hτ]
  <;> ring

section ConditionalStep

variable {Ω : Type*} [MeasurableSpace Ω] [CompleteSpace E]

lemma expected_functional_change (P : Measure Ω) [IsProbabilityMeasure P]
    (F ψ : E → ℝ) {μ τ γ α variance : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hα : α = μ * γ)
    (xstar x y m z g b : E) (mnext znext ζ : Ω → E)
    (hζ : Integrable ζ P)
    (hζsq : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hζzero : (∫ ω, ζ ω ∂P) = 0)
    (hζvariance : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance)
    (hE : Integrable (fun ω => functionalEnergy F ψ μ τ xstar y (mnext ω) (znext ω)) P)
    (hupdate : ∀ᵐ ω ∂P, mnext ω = m + α • (g - m + b + ζ ω))
    (hsmooth : F y - F x ≤ -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2)
    (hsupport : ∀ᵐ ω ∂P,
      ψ z + ⟪τ⁻¹ • (x - z) - m, znext ω - z⟫_ℝ ≤ ψ (znext ω)) :
    (∫ ω, functionalEnergy F ψ μ τ xstar y (mnext ω) (znext ω) ∂P) -
        functionalEnergy F ψ μ τ xstar x m z ≤
      componentBound F ψ μ τ γ α xstar x y m z g b +
        μ * γ ^ 2 / 2 * variance := by
  have hi₁ : Integrable (fun ω => ⟪x - z, ζ ω⟫_ℝ) P :=
    Integrable.const_inner (x - z) hζ
  have hi₂ : Integrable (fun ω => ⟪y - xstar, ζ ω⟫_ℝ) P :=
    Integrable.const_inner (y - xstar) hζ
  have hi₃ : Integrable (fun ω => ⟪g - m + b, ζ ω⟫_ℝ) P :=
    Integrable.const_inner (g - m + b) hζ
  have hz₁ : (∫ ω, ⟪x - z, ζ ω⟫_ℝ ∂P) = 0 := by
    rw [integral_inner hζ, hζzero, inner_zero_right]
  have hz₂ : (∫ ω, ⟪y - xstar, ζ ω⟫_ℝ ∂P) = 0 := by
    rw [integral_inner hζ, hζzero, inner_zero_right]
  have hz₃ : (∫ ω, ⟪g - m + b, ζ ω⟫_ℝ ∂P) = 0 := by
    rw [integral_inner hζ, hζzero, inner_zero_right]
  have hpoint : ∀ᵐ ω ∂P,
      functionalEnergy F ψ μ τ xstar y (mnext ω) (znext ω) -
          functionalEnergy F ψ μ τ xstar x m z ≤
        componentBound F ψ μ τ γ α xstar x y m z g b +
          γ / τ * ⟪x - z, ζ ω⟫_ℝ - α / 8 * ⟪y - xstar, ζ ω⟫_ℝ +
          μ * γ ^ 2 * ⟪g - m + b, ζ ω⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ ω‖ ^ 2 := by
    filter_upwards [hupdate, hsupport] with ω hu hs
    exact functional_change_with_noise F ψ hμ hτ hα
      xstar x y m (mnext ω) z (znext ω) g b (ζ ω) hu hsmooth hs
  have hleft := hE.sub (integrable_const (functionalEnergy F ψ μ τ xstar x m z))
  have hright := (((integrable_const
      (componentBound F ψ μ τ γ α xstar x y m z g b)).add
      (hi₁.const_mul (γ / τ))).sub (hi₂.const_mul (α / 8))).add
      (hi₃.const_mul (μ * γ ^ 2))
  have hright' := hright.add (hζsq.const_mul (μ * γ ^ 2 / 2))
  have h := integral_mono_ae hleft hright' hpoint
  rw [integral_sub hE (integrable_const _)] at h
  rw [integral_add hright (hζsq.const_mul _),
    integral_add _ (hi₃.const_mul _), integral_sub _ (hi₂.const_mul _),
    integral_add (integrable_const _) (hi₁.const_mul _)] at h
  simp only [integral_const, probReal_univ, one_smul, smul_eq_mul,
    integral_const_mul, hz₁, hz₂, hz₃, mul_zero, add_zero, sub_zero] at h
  have hv := mul_le_mul_of_nonneg_left hζvariance
    (show 0 ≤ μ * γ ^ 2 / 2 by positivity)
  linarith

end ConditionalStep

end LongTails.Proofs.ProximalEf21FunctionalCalculus
