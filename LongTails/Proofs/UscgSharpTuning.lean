import LongTails.Algorithms.UscgSharpConfidence
import Mathlib.Tactic

namespace LongTails.Proofs.UscgSharpTuning

open LongTails.Algorithms.UscgSharpConfidence
open LongTails.Setups.UscgHighProbability

lemma inverseMemory_ge_two (p : Public) : 2 ≤ inverseMemory p := by
  unfold inverseMemory
  have h : 0 ≤ 65536 * p.ζ ^ 2 * p.σ ^ 2 / p.ε ^ 2 := by positivity
  linarith

lemma memory_pos_lt_one (p : Public) : 0 < 1 / inverseMemory p ∧ 1 / inverseMemory p < 1 := by
  have ha := inverseMemory_ge_two p
  constructor
  · positivity
  · exact (div_lt_one (by linarith)).mpr (by linarith)

lemma memory_noise (p : Public) (he : 0 < p.ε) (hz : 0 < p.ζ) :
    (1 / inverseMemory p) * p.σ ^ 2 ≤ (p.ε / (256 * p.ζ)) ^ 2 := by
  have ha := inverseMemory_ge_two p
  have hap : 0 < inverseMemory p := by linarith
  have hid : inverseMemory p * p.ε ^ 2 = 2 * p.ε ^ 2 + 65536 * p.ζ ^ 2 * p.σ ^ 2 := by
    unfold inverseMemory
    field_simp
  have heq : (p.ε / (256 * p.ζ)) ^ 2 = p.ε ^ 2 / (65536 * p.ζ ^ 2) := by
    field_simp
    ring
  rw [heq]
  apply (le_div_iff₀ (show 0 < 65536 * p.ζ ^ 2 by positivity)).mpr
  have hmul : (1 / inverseMemory p) * p.σ ^ 2 * (65536 * p.ζ ^ 2) ≤ p.ε ^ 2 := by
    have hh : (65536 * p.ζ ^ 2 * p.σ ^ 2) / inverseMemory p ≤ p.ε ^ 2 :=
      (div_le_iff₀ hap).mpr (by nlinarith)
    convert hh using 1
    ring
  exact hmul

lemma margin_from_parts {α η ζ G s e K Δ L ℓ : ℝ}
    (hα : 0 < α) (hη : 0 ≤ η) (hζ : 0 < ζ) (hK : 0 ≤ K)
    (hscale : η * e * K = 4 * Δ)
    (hnoise : 10 * ζ * s ≤ e / 16)
    (htail : 2 * G + 8 * G / α * ℓ + 2 * G / α ≤ e * K / 16)
    (htrack : 2 * L * η / α ≤ e / 16) (hsmooth : L * η ≤ e / 8) :
    η * (2 * ζ * (5 * s * K + (4 * (G / ζ) / α) * ℓ + G / ζ) +
      2 * (G + K * (L * η)) / α) + K * (L * η ^ 2 / 2) ≤ Δ := by
  have hn := mul_le_mul_of_nonneg_right hnoise hK
  have ht := mul_le_mul_of_nonneg_right htrack hK
  have hb : 2 * ζ * (5 * s * K + (4 * (G / ζ) / α) * ℓ + G / ζ) +
      2 * (G + K * (L * η)) / α ≤ 3 * e * K / 16 := by
    have heq : 2 * ζ * (5 * s * K + (4 * (G / ζ) / α) * ℓ + G / ζ) +
        2 * (G + K * (L * η)) / α =
        (10 * ζ * s) * K + (2 * G + 8 * G / α * ℓ + 2 * G / α) +
          (2 * L * η / α) * K := by
      field_simp
      ring
    rw [heq]
    linarith
  have hm := mul_le_mul_of_nonneg_left hb hη
  have hc := mul_le_mul_of_nonneg_left hsmooth (show 0 ≤ K * η / 2 by positivity)
  nlinarith

lemma confidence_log_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.log (1 / δ) := by
  apply Real.log_nonneg
  exact (le_div_iff₀ hδ).mpr (by simpa using hδ1)

lemma horizon_lower (p : Public) (hhard : ¬2 * p.L * p.Δ ≤ p.ε ^ 2) :
    4096 * inverseMemory p * (1 + p.L * p.Δ / p.ε ^ 2 +
      Real.sqrt (p.L * p.Δ / p.ε ^ 2) * (1 + Real.log (1 / p.δ))) ≤ horizon p := by
  unfold horizon
  rw [ite_eq_right hhard]
  exact Nat.le_ceil _

lemma horizon_pos (p : Public) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ)
    (hδ : 0 < p.δ) (hδ1 : p.δ ≤ 1) : 0 < horizon p := by
  unfold horizon
  split_ifs with hh
  · norm_num
  · apply Nat.ceil_pos.mpr
    have ha := inverseMemory_ge_two p
    have hD : 0 ≤ p.L * p.Δ / p.ε ^ 2 := by positivity
    have hlog := confidence_log_nonneg hδ hδ1
    positivity

lemma count_parts {a D r ℓ K e v : ℝ} (ha : 2 ≤ a) (hD : 0 ≤ D)
    (hr : 0 ≤ r) (hℓ : 0 ≤ ℓ) (hK : 0 < K) (he : 0 < e) (hv : 0 ≤ v)
    (hcount : 4096 * a * (1 + D + r * (1 + ℓ)) ≤ K)
    (hscale : v * K = 4 * e * D) :
    2 * a * v ≤ e / 16 ∧ v ≤ e / 8 ∧
      2 * (2 * e * r) + 8 * a * (2 * e * r) * ℓ + 2 * a * (2 * e * r) ≤ e * K / 16 := by
  have ha0 : 0 ≤ a := by linarith
  have hR : 0 ≤ r * (1 + ℓ) := by positivity
  have hKD : 128 * a * D ≤ K := by
    nlinarith [mul_nonneg ha0 hD, mul_nonneg ha0 hR]
  have hKR : 256 * a * r * (1 + ℓ) ≤ K := by
    nlinarith [mul_nonneg ha0 hD, mul_nonneg ha0 hR]
  have htrack : 2 * a * v ≤ e / 16 := by
    apply (mul_le_mul_iff_right₀ hK).mp
    have hh := mul_le_mul_of_nonneg_left hKD he.le
    have hs := congrArg (fun z : ℝ => 2 * a * z) hscale
    nlinarith
  refine ⟨htrack, ?_, ?_⟩
  · have hh : v ≤ 2 * a * v := by nlinarith
    linarith
  · have har := mul_le_mul_of_nonneg_right ha hr
    have hsmall : 4 * r + 16 * a * r * ℓ + 4 * a * r ≤ K / 16 := by
      nlinarith [mul_nonneg (mul_nonneg ha0 hr) hℓ]
    have hh := mul_le_mul_of_nonneg_left hsmall he.le
    nlinarith

end LongTails.Proofs.UscgSharpTuning
