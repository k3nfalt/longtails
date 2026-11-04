import Mathlib

namespace LongTails.Proofs.UscgSharpMixingConstants

lemma logarithmic_ratio_bound {r : ℝ} (hr : 256 ≤ r) :
    (Real.log (4 * r) + 2) / r ≤ 3 / 64 := by
  have hr0 : 0 < r := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog1024 : Real.log 1024 ≤ 10 := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have he : 4 * r = 1024 * (r / 256) := by ring
  have hlog : Real.log (4 * r) ≤ 9 + r / 256 := by
    rw [he, Real.log_mul (by norm_num) (by positivity)]
    have hh := Real.log_le_sub_one_of_pos (show 0 < r / 256 by positivity)
    linarith
  apply (div_le_iff₀ hr0).mpr
  nlinarith

lemma radius_bounds {a p : ℝ} (ha : 0 < a) (hp : 0 < p)
    (hr : 256 ≤ a / p) :
    1 ≤ 4 * a / p ∧
    0 < (Real.log (4 * a / p) + 2) / a ∧
    p * ((Real.log (4 * a / p) + 2) / a) ≤ 3 / 64 := by
  have hC : 1 ≤ 4 * a / p := by
    rw [show 4 * a / p = 4 * (a / p) by ring]
    linarith
  refine ⟨hC, div_pos (by linarith [Real.log_nonneg hC]) ha, ?_⟩
  have hh := logarithmic_ratio_bound hr
  have he : p * ((Real.log (4 * a / p) + 2) / a) =
      (Real.log (4 * (a / p)) + 2) / (a / p) := by
    rw [show 4 * (a / p) = 4 * a / p by ring]
    field_simp
  rwa [he]

lemma probability_constants {p R : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hpR : p * R ≤ 3 / 64) :
    2 * Real.exp 1 * p * R ≤ 9 / 32 ∧
    2 * Real.exp 1 * p * R < 1 / 3 ∧
    1 < Real.log ((1 / (2 * R)) / p) ∧
    (2 * Real.exp 1 * p * R) / (1 - 2 * Real.exp 1 * p * R) < 1 / 2 := by
  have hq : 2 * Real.exp 1 * p * R ≤ 9 / 32 := by
    have hmul := mul_le_mul_of_nonneg_left hpR (show 0 ≤ 2 * Real.exp 1 by positivity)
    nlinarith [Real.exp_one_lt_three]
  have hq3 : 2 * Real.exp 1 * p * R < 1 / 3 := by linarith
  have hratio : Real.exp 1 < (1 / (2 * R)) / p := by
    apply (lt_div_iff₀ hp).mpr
    apply (lt_div_iff₀ (show 0 < 2 * R by positivity)).mpr
    nlinarith
  have hlog : 1 < Real.log ((1 / (2 * R)) / p) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hratio
  refine ⟨hq, hq3, hlog, ?_⟩
  apply (div_lt_iff₀ (show 0 < 1 - 2 * Real.exp 1 * p * R by linarith)).mpr
  linarith

lemma public_threshold {A a : ℝ} (hA : 8192 ≤ A)
    (ha : 4096 / (A + 16) ≤ a) :
    0 < 16 / (A + 16) ∧ 16 / (A + 16) ≤ 1 ∧
    0 < a ∧ 256 ≤ a / (16 / (A + 16)) := by
  have hden : 0 < A + 16 := by linarith
  have hp : 0 < 16 / (A + 16) := by positivity
  have hlow : 0 < 4096 / (A + 16) := by positivity
  refine ⟨hp, (div_le_one hden).mpr (by linarith), lt_of_lt_of_le hlow ha, ?_⟩
  apply (le_div_iff₀ hp).mpr
  have he : 256 * (16 / (A + 16)) = 4096 / (A + 16) := by ring
  rwa [he]

end LongTails.Proofs.UscgSharpMixingConstants
