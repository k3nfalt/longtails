import LongTails.Proofs.SharpEnvelopeEnergy

namespace LongTails.Proofs.SharpEnvelopeTuning

lemma energy_coefficient {L μ θ τ : ℝ} (hμ : 0 < μ)
    (hθ : 0 < θ) (hτ1 : τ ≤ 1) (hsmall : θ ≤ τ / 8)
    (hscale : 1 / (4 * L) = θ ^ 2 / μ) :
    θ / (2 * μ) + 3 / (4 * L) + θ ^ 3 / (2 * μ * (1 - θ ^ 2)) ≤
      θ / (2 * μ) * (1 + τ) := by
  have ht : θ ≤ 1 / 8 := by linarith
  have hd : 0 < 1 - θ ^ 2 := by nlinarith
  have hratio : θ ^ 2 / (1 - θ ^ 2) ≤ 2 * θ := by
    apply (div_le_iff₀ hd).mpr
    have hsq : θ ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hθ.le]
  have hb : 1 + 6 * θ + θ ^ 2 / (1 - θ ^ 2) ≤ 1 + τ := by linarith
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ θ / (2 * μ) by positivity)
  have hid : θ / (2 * μ) + 3 / (4 * L) + θ ^ 3 / (2 * μ * (1 - θ ^ 2)) =
      θ / (2 * μ) * (1 + 6 * θ + θ ^ 2 / (1 - θ ^ 2)) := by
    rw [show 3 / (4 * L) = 3 * (1 / (4 * L)) by ring, hscale]
    field_simp; ring
  rw [hid]
  exact hh

lemma error_absorption {L μ θ τ β : ℝ} (hμ : 0 < μ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : 1 / (4 * L) = θ ^ 2 / μ) :
    (θ / (2 * μ) * (1 + τ)) * (1 + 1 / τ) * β ^ 2 ≤ 1 / (4 * L) := by
  rw [hscale]
  have hc : 0 ≤ θ / (2 * μ) * (1 + τ) * (1 + 1 / τ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hnoise hc
  have hid : (θ / (2 * μ) * (1 + τ) * (1 + 1 / τ)) * (τ * θ / 2) =
      θ ^ 2 / (4 * μ) * (1 + τ) ^ 2 := by field_simp; ring
  rw [hid] at hh
  have hs : (1 + τ) ^ 2 ≤ 4 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hs (show 0 ≤ θ ^ 2 / (4 * μ) by positivity)
  have he : θ ^ 2 / (4 * μ) * 4 = θ ^ 2 / μ := by ring
  rw [he] at ht
  exact hh.trans ht

end LongTails.Proofs.SharpEnvelopeTuning
