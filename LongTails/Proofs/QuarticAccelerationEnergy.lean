import LongTails.Proofs.QuarticAcceleration

namespace LongTails.Proofs.QuarticAccelerationEnergy

open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open LongTails.Proofs.CompositeCubicAcceleration hiding advance_certificate
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma initial_trial_weight {μ : ℝ} (hμ : 0 < μ) : trialWeight μ 0 = μ⁻¹ := by
  simp only [trialWeight, mul_zero, add_zero, Real.sqrt_one]
  field_simp
  ring

lemma initial_center {μ : ℝ} (hμ : 0 < μ) (x0 : E) : center E μ ⟨0, x0, x0⟩ = x0 := by
  simp [center, initial_trial_weight hμ, hμ.ne']

lemma initial_advance {μ γ : ℝ} (hμ : 0 < μ) (x0 y g : E)
    (hlam : parameter E γ x0 y = μ) :
    advance E μ γ ⟨0, x0, x0⟩ y g = ⟨μ⁻¹, y, x0 - μ⁻¹ • g⟩ := by
  have hd : damping E μ γ ⟨0, x0, x0⟩ y = 1 := by
    simp only [damping, initial_center hμ, hlam, div_self hμ.ne', min_self]
  simp [advance, hd, initial_trial_weight hμ, hμ.ne']

lemma weight_bounds (s : State E) {μ γ : ℝ} {y g : E}
    (hμ : 0 < μ) (hA : 0 ≤ s.weight) (hlam : 0 < parameter E γ (center E μ s) y) :
    s.weight < (advance E μ γ s y g).weight ∧
      (advance E μ γ s y g).weight ≤ s.weight + trialWeight μ s.weight := by
  have hb := damping_properties hμ hlam
  change s.weight < s.weight + damping E μ γ s y * trialWeight μ s.weight ∧ _
  have ha := trialWeight_pos hμ hA
  constructor
  · exact lt_add_of_pos_right _ (mul_pos hb.1 ha)
  · change s.weight + damping E μ γ s y * trialWeight μ s.weight ≤ _
    have hh := mul_le_mul_of_nonneg_right hb.2.1 ha.le
    simpa only [one_mul, damping, add_comm] using add_le_add_left hh s.weight

lemma trial_coefficient {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) :
    1 ≤ (A + trialWeight μ A) * μ := by
  have hh := mul_le_mul_of_nonneg_right (trialWeight_lower hμ hA) hμ.le
  rw [inv_mul_cancel₀ hμ.ne'] at hh
  nlinarith only [hh, mul_nonneg hA hμ.le]

lemma up_energy {μ γ A r : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A)
    (hup : μ < γ * r ^ 2) :
    (A + min 1 (μ / (γ * r ^ 2)) * trialWeight μ A) * μ ^ 2 ≤
      γ * ((A + trialWeight μ A) * min μ (γ * r ^ 2) * r ^ 2) := by
  have hlam : 0 < γ * r ^ 2 := hμ.trans hup
  have hb := damping_properties hμ hlam
  have ha := trialWeight_pos hμ hA
  have hweight : A + min 1 (μ / (γ * r ^ 2)) * trialWeight μ A ≤ A + trialWeight μ A := by
    have hh := mul_le_mul_of_nonneg_right hb.2.1 ha.le
    nlinarith only [hh]
  have hT : 0 ≤ A + trialWeight μ A := by linarith
  have hfirst := mul_le_mul_of_nonneg_right hweight (sq_nonneg μ)
  have hsecond := mul_le_mul_of_nonneg_left hup.le (mul_nonneg hT hμ.le)
  rw [min_eq_left hup.le]
  nlinarith only [hfirst, hsecond]

lemma dissipation_radius {R r coeff rest : ℝ} (hrest : 0 ≤ rest) (hc : 1 ≤ coeff)
    (henergy : rest + (1 - (1 / 32 : ℝ) ^ 2) * coeff * r ^ 2 / 2 ≤ R ^ 2 / 2) :
    r ^ 2 ≤ 2 * R ^ 2 := by
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
  nlinarith only [henergy, hrest, hh, sq_nonneg R]

lemma movement_radius {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hbound : r ^ 2 ≤ 8 * R ^ 2) :
    r ≤ 3 * R := by nlinarith

end LongTails.Proofs.QuarticAccelerationEnergy
