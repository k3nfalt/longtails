import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace LongTails.Proofs.AdamSymmetricGeometry

lemma bounded_noise_denominator_envelope {R k μ N s h D : ℝ}
    (hk : 0 ≤ k) (hk₁ : k ≤ 1) (hN : |N| ≤ s) (hs : s ≤ h)
    (hR : R ≤ D) (hA : k * |μ + N| ≤ D) :
    R + k * (|μ| + s) ≤ 2 * D + 2 * h := by
  have hs₀ : 0 ≤ s := (abs_nonneg _).trans hN
  have hμ : |μ| ≤ |μ + N| + s := by
    calc
      |μ| = |(μ + N) - N| := by congr 1; ring
      _ ≤ |μ + N| + |N| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (μ + N) (-N)
      _ ≤ |μ + N| + s := add_le_add (le_refl _) hN
  have hm := mul_le_mul_of_nonneg_left hμ hk
  have hks : k * s ≤ h := (mul_le_of_le_one_left hs₀ hk₁).trans hs
  nlinarith

lemma bounded_noise_direction_envelope {H D h t δ : ℝ}
    (ht : 1 ≤ t) (hh : 0 ≤ h)
    (hH : H ≤ 2 * D + 2 * h)
    (hδ : |δ| ≤ 2 * t) (hDδ : D * |δ| ≤ h * (1 + t)) :
    H * |δ| ≤ 8 * h * t := by
  have h₁ := mul_le_mul_of_nonneg_right hH (abs_nonneg δ)
  have h₂ := mul_le_mul_of_nonneg_left hδ hh
  have h₃ := mul_le_mul_of_nonneg_left ht hh
  nlinarith

lemma symmetric_pair_absolute_lower (m x : ℝ) :
    2 * |x| ≤ |m + x| + |m - x| := by
  have heq : (m + x) - (m - x) = 2 * x := by ring
  have h : |(m + x) - (m - x)| ≤ |m + x| + |m - x| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (m + x) (-(m - x))
  rw [heq, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at h
  exact h

lemma normalized_direction_bound {m v τ t : ℝ} (hv : 0 ≤ v) (hτ : 0 ≤ τ)
    (ht : 0 ≤ t) (hm : |m| ≤ t * v) : |m / (v + τ)| ≤ t := by
  by_cases hden : v + τ = 0
  · simp [hden, ht]
  · have hpos : 0 < v + τ := lt_of_le_of_ne (by positivity) (Ne.symm hden)
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact hm.trans (mul_le_mul_of_nonneg_left (by linarith) ht)

lemma normalized_direction_product {m v τ t : ℝ} (hv : 0 ≤ v) (hτ : 0 ≤ τ)
    (hm : |m| ≤ t * v) : (v + τ) * (m / (v + τ)) = m := by
  by_cases hden : v + τ = 0
  · have hv0 : v = 0 := by linarith
    have hm0 : m = 0 := by simpa [hv0] using hm
    simp [hden, hm0]
  · field_simp

lemma normalized_pair_envelope {m₁ m₂ v₁ v₂ τ h t : ℝ}
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hτ : 0 ≤ τ) (ht : 0 ≤ t)
    (hm₁ : |m₁| ≤ t * v₁) (hm₂ : |m₂| ≤ t * v₂)
    (hm : |m₁ - m₂| ≤ h) (hv : |v₁ - v₂| ≤ h) :
    |m₁ / (v₁ + τ) - m₂ / (v₂ + τ)| ≤ 2 * t ∧
      (v₂ + τ) * |m₁ / (v₁ + τ) - m₂ / (v₂ + τ)| ≤ h * (1 + t) := by
  have h₁ := normalized_direction_bound hv₁ hτ ht hm₁
  have h₂ := normalized_direction_bound hv₂ hτ ht hm₂
  have hp₁ := normalized_direction_product hv₁ hτ hm₁
  have hp₂ := normalized_direction_product hv₂ hτ hm₂
  constructor
  · calc
      |m₁ / (v₁ + τ) - m₂ / (v₂ + τ)| ≤
          |m₁ / (v₁ + τ)| + |m₂ / (v₂ + τ)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (m₁ / (v₁ + τ)) (-(m₂ / (v₂ + τ)))
      _ ≤ 2 * t := by linarith
  · have heq : (v₂ + τ) * (m₁ / (v₁ + τ) - m₂ / (v₂ + τ)) =
        (m₁ - m₂) + (m₁ / (v₁ + τ)) * (v₂ - v₁) := by nlinarith
    have ha := abs_add_le (m₁ - m₂) ((m₁ / (v₁ + τ)) * (v₂ - v₁))
    rw [← heq, abs_mul, abs_of_nonneg (show 0 ≤ v₂ + τ by positivity)] at ha
    have hx : |(m₁ / (v₁ + τ)) * (v₂ - v₁)| ≤ t * h := by
      rw [abs_mul]
      exact mul_le_mul h₁ (by simpa only [abs_sub_comm] using hv) (abs_nonneg _) ht
    nlinarith

end LongTails.Proofs.AdamSymmetricGeometry
