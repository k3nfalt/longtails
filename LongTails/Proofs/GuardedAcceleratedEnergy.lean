import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.GuardedAcceleratedEnergy

lemma estimate_minimum_step {a μ φ f₀ f₁ f₂ g₀ g₁ r₀ r₁ G : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hμ : 0 ≤ μ)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hφ : f₀ ≤ φ) (hsupport : f₁ + g₀ + μ * r₀ / 2 ≤ f₀)
    (hcancel : g₀ + a * g₁ = 0)
    (hdescent : f₂ ≤ f₁ - a ^ 2 / (2 * μ) * G) :
    f₂ ≤ (1 - a) * φ + a * f₁ + μ * a * (1 - a) * r₁ / 2 +
      a * (1 - a) * g₁ - a ^ 2 / (2 * μ) * G := by
  have hweight : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hleft := mul_le_mul_of_nonneg_left (le_trans hsupport hφ) hweight
  have hnorm₀ : 0 ≤ (1 - a) * μ * r₀ / 2 := by positivity
  have hnorm₁ : 0 ≤ μ * a * (1 - a) * r₁ / 2 := by positivity
  have hc : (1 - a) * g₀ + a * (1 - a) * g₁ = 0 := by
    calc
      _ = (1 - a) * (g₀ + a * g₁) := by ring
      _ = 0 := by rw [hcancel, mul_zero]
  nlinarith

lemma estimate_center_step {a φc Fc ℓc : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hφ : φc ≤ Fc) (hℓ : ℓc ≤ Fc) :
    (1 - a) * φc + a * ℓc ≤ Fc := by
  have h1 := mul_le_mul_of_nonneg_left hφ (sub_nonneg.mpr ha1)
  have h2 := mul_le_mul_of_nonneg_left hℓ ha
  nlinarith

lemma displacement_of_estimate {μ φc φmin Fc Fx r : ℝ}
    (hμ : 0 < μ) (hcenter : φc ≤ Fc) (hminimum : Fx ≤ φmin)
    (hquadratic : φc = φmin + μ * r / 2) :
    r ≤ 2 * (Fc - Fx) / μ := by
  apply (le_div_iff₀ hμ).mpr
  nlinarith

lemma truncated_gradient_progress {L r G Fy Fc Fnew : ℝ}
    (hr : 0 < r)
    (hG : L * r / 2 < G)
    (hsupport : Fy ≤ Fc + G * r / 8)
    (hdescent : Fnew ≤ Fy - G * r / 2 + L * r ^ 2 / 8) :
    Fnew ≤ Fc - L * r ^ 2 / 16 := by
  have hGr := mul_lt_mul_of_pos_right hG hr
  nlinarith

lemma restart_drop {N q μ r D C : ℝ}
    (hq : 0 < q) (hC : 0 < C)
    (hD : 0 ≤ D) (hprogress : N * q ≤ D)
    (hmovement : μ * r ^ 2 ≤ C * N * D) :
    μ * q * r ^ 2 ≤ C * D ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right hmovement hq.le
  have h2 := mul_le_mul_of_nonneg_right hprogress (mul_nonneg hC.le hD)
  nlinarith

end LongTails.Proofs.GuardedAcceleratedEnergy
