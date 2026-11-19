import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.BlumGladyshevMask

noncomputable def probability (G B R ε : ℝ) : ℝ :=
  2 ^ 24 * ε ^ 2 / ((G ^ 2 + B ^ 2 * R ^ 2) * R ^ 2)

lemma mask_bounds {G B R ε : ℝ} (hG : 0 < G) (hR : 0 < R) (hε : 0 < ε)
    (hscale : 65536 * ε ≤ G * R) :
    0 < probability G B R ε ∧ probability G B R ε ≤ 1 / 256 := by
  have hd : 0 < (G ^ 2 + B ^ 2 * R ^ 2) * R ^ 2 := by positivity
  refine ⟨div_pos (by positivity) hd, (div_le_iff₀ hd).2 ?_⟩
  have h := pow_le_pow_left₀ (show 0 ≤ 65536 * ε by positivity) hscale 2
  nlinarith only [h, mul_nonneg (sq_nonneg B) (pow_nonneg hR.le 4)]

lemma prefix_failure {q δ : ℝ} {N : ℕ} (hq : 0 < q) (hq' : q ≤ 1 / 8)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hN : (N : ℝ) * q ≤ Real.log (1 / δ) / 16) :
    2 * δ < (1 - q) ^ (N + 1) := by
  have hpos : 0 < 1 - q := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
  rw [Real.log_inv] at hl
  have hr : (1 - q)⁻¹ - 1 ≤ 2 * q := by
    rw [sub_le_iff_le_add, inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hq.le (show 0 ≤ 1 / 8 - q by linarith)]
  have hlog : -(2 * q) ≤ Real.log (1 - q) := by linarith
  have hδ8 : (8 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith)
  have h3 : 3 * Real.log 2 ≤ Real.log (1 / δ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hδ8
    rwa [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Nat.cast_ofNat] at hh
  have h2 := Real.log_le_sub_one_of_pos (show 0 < (1 / 2 : ℝ) by norm_num)
  rw [one_div, Real.log_inv] at h2
  apply (Real.log_lt_log_iff (by positivity) (pow_pos hpos _)).mp
  rw [Real.log_mul (by norm_num) hδ.ne', Real.log_pow, Nat.cast_succ]
  rw [one_div, Real.log_inv] at h3 hN
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (N : ℝ) + 1 by positivity)
  nlinarith only [h3, hN, hq', hh, h2]

lemma budget_times_probability {G B R ε δ : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R)
    (hε : 0 < ε) (hn : (n : ℝ) ≤
      R ^ 2 * (G ^ 2 + B ^ 2 * R ^ 2) * Real.log (1 / δ) / (2 ^ 28 * ε ^ 2)) :
    (n : ℝ) * probability G B R ε ≤ Real.log (1 / δ) / 16 := by
  have hd : 0 < (G ^ 2 + B ^ 2 * R ^ 2) * R ^ 2 := by positivity
  unfold probability
  rw [mul_div_assoc', div_le_iff₀ hd]
  have hh := (le_div_iff₀ (show 0 < 2 ^ 28 * ε ^ 2 by positivity)).mp hn
  linarith only [hh]

end LongTails.Proofs.BlumGladyshevMask
