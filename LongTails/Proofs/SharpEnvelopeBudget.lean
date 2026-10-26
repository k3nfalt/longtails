import LongTails.Proofs.SharpEnvelopeParameters
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.SharpEnvelopeBudget

open LongTails.Algorithms.SharpEnvelope SharpEnvelopeParameters

noncomputable def base (T : ℝ) : ℕ := ⌈32 * (1 + Real.log (2 + T))⌉₊

noncomputable def depth (T : ℝ) : ℕ := ⌈Real.log (2 + T) / Real.log (ratio (base T))⌉₊

lemma base_bounds {T : ℝ} (hT : 0 ≤ T) :
    32 ≤ base T ∧ 32 * (1 + Real.log (2 + T)) ≤ (base T : ℝ) ∧
      (base T : ℝ) ≤ 33 * (1 + Real.log (2 + T)) := by
  have hl : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hc := Nat.le_ceil (32 * (1 + Real.log (2 + T)))
  have hu := Nat.ceil_lt_add_one (by positivity : 0 ≤ 32 * (1 + Real.log (2 + T)))
  have hb : (32 : ℝ) ≤ base T := by change _ ≤ (⌈32 * (1 + Real.log (2 + T))⌉₊ : ℝ); linarith
  refine ⟨by exact_mod_cast hb, hc, ?_⟩
  change (⌈32 * (1 + Real.log (2 + T))⌉₊ : ℝ) ≤ _
  linarith

lemma ratio_log {b : ℕ} (hb : 1 ≤ b) : 1 < Real.log (ratio b) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (1 : ℝ) ≤ (b : ℝ) ^ 32 := one_le_pow₀ hbR
  have hr : 3 ≤ ratio b := by unfold ratio; linarith
  have he : Real.exp 1 < ratio b := Real.exp_one_lt_three.trans_le hr
  have hh := Real.log_lt_log (Real.exp_pos 1) he
  simpa only [Real.log_exp] using hh

lemma depth_bounds {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ depth T ∧ (depth T : ℝ) ≤ 1 + Real.log (2 + T) ∧
      16 * ((depth T : ℝ) + 1) ≤ (base T : ℝ) := by
  have hb := base_bounds hT
  have hlog := ratio_log (by omega : 1 ≤ base T)
  have hu : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  have hd : 0 < Real.log (2 + T) / Real.log (ratio (base T)) := div_pos hu (by linarith)
  have hceil := Nat.ceil_lt_add_one hd.le
  have hr : Real.log (2 + T) / Real.log (ratio (base T)) ≤ Real.log (2 + T) := by
    apply div_le_self hu.le (by linarith)
  have hdepth : (depth T : ℝ) ≤ 1 + Real.log (2 + T) := by
    change (⌈Real.log (2 + T) / Real.log (ratio (base T))⌉₊ : ℝ) ≤ _
    linarith
  refine ⟨?_, hdepth, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.ceil_pos.mpr hd))
  · linarith [hb.2.1]

lemma depth_scale {T : ℝ} (hT : 0 ≤ T) :
    2 + T ≤ ratio (base T) ^ depth T ∧
      ratio (base T) ^ depth T ≤ ratio (base T) * (2 + T) := by
  have hb := base_bounds hT
  have hq := ratio_pos (by omega : 1 ≤ base T)
  have hl := ratio_log (by omega : 1 ≤ base T)
  have hu : 0 < 2 + T := by linarith
  have hratio : 0 ≤ Real.log (2 + T) / Real.log (ratio (base T)) := by
    apply div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hlo := Nat.le_ceil (Real.log (2 + T) / Real.log (ratio (base T)))
  have hhi := (Nat.ceil_lt_add_one hratio).le
  have hlo' := mul_le_mul_of_nonneg_right hlo (by linarith : 0 ≤ Real.log (ratio (base T)))
  have hhi' := mul_le_mul_of_nonneg_right hhi (by linarith : 0 ≤ Real.log (ratio (base T)))
  have he : Real.log (2 + T) / Real.log (ratio (base T)) * Real.log (ratio (base T)) =
      Real.log (2 + T) := div_mul_cancel₀ _ (by linarith)
  rw [he] at hlo'
  rw [add_mul, he, one_mul] at hhi'
  constructor
  · apply (Real.log_le_log_iff hu (pow_pos hq _)).mp
    rw [Real.log_pow]
    exact hlo'
  · apply (Real.log_le_log_iff (pow_pos hq _) (mul_pos hq hu)).mp
    rw [Real.log_pow, Real.log_mul (ne_of_gt hq) (ne_of_gt hu)]
    change (depth T : ℝ) * Real.log (ratio (base T)) ≤ _ at hhi'
    linarith

lemma public_noise {T α : ℝ} (hT : 0 ≤ T)
    (hα : α ≤ 1 / (100 * (33 * (1 + Real.log (2 + T))) ^ 12)) :
    α ≤ precision (base T) (depth T) 0 := by
  have hb := base_bounds hT
  have hb0 : (0 : ℝ) < base T := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 32) hb.1)
  have hp := pow_le_pow_left₀ hb0.le hb.2.2 12
  have hdiv := one_div_le_one_div_of_le (by positivity : 0 < 100 * (base T : ℝ) ^ 12)
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 100))
  simpa only [precision, Nat.cast_zero, zero_div, add_zero] using hα.trans hdiv


lemma gradient_calls (n i : ℕ) : gradientCalls n i = (2 * n) ^ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [gradientCalls, ih, pow_succ]; ring

lemma recovery_calls {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    recoveryCalls n i ≤ 2 * (2 * n) ^ i := by
  induction i with
  | zero => simp [recoveryCalls]
  | succ i ih =>
      rw [recoveryCalls, gradient_calls, pow_succ]
      have hh := Nat.mul_le_mul_right ((2 * n) ^ i) (show 2 ≤ 2 * n by omega)
      nlinarith

lemma phase_power {b : ℕ} (hb : 2 ≤ b) :
    (2 * (b : ℝ) ^ 20) ^ 8 ≤ ratio b ^ 5 := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hp : (b : ℝ) ≤ (b : ℝ) ^ 32 := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ b) (show 1 ≤ 32 by omega)
  have hq : 7 / 2 * (b : ℝ) ^ 32 ≤ ratio b := by unfold ratio; linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 7 / 2 * (b : ℝ) ^ 32) hq 5
  nlinarith only [hs, pow_nonneg hb0 160]

lemma recursive_power {b : ℕ} (hb : 2 ≤ b) (d : ℕ) :
    (2 * (b : ℝ) ^ 20) ^ d ≤ (ratio b ^ d) ^ (5 / 8 : ℝ) := by
  have hq := ratio_pos (by omega : 1 ≤ b)
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (2 * (b : ℝ) ^ 20) ^ 8) (phase_power hb) d
  have hp : ((2 * (b : ℝ) ^ 20) ^ d) ^ 8 ≤ (ratio b ^ d) ^ 5 := by
    simpa only [← pow_mul, Nat.mul_comm] using hh
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ ((2 * (b : ℝ) ^ 20) ^ d) ^ 8) hp
    (by norm_num : (0 : ℝ) ≤ 1 / 8)
  rw [← Real.rpow_natCast ((2 * (b : ℝ) ^ 20) ^ d) 8,
    ← Real.rpow_natCast (ratio b ^ d) 5,
    ← Real.rpow_mul (by positivity : 0 ≤ (2 * (b : ℝ) ^ 20) ^ d),
    ← Real.rpow_mul (pow_pos hq d).le] at hr
  norm_num at hr
  exact hr

lemma ratio_power {b : ℕ} (hb : 1 ≤ b) :
    ratio b ^ (5 / 8 : ℝ) ≤ 4 * (b : ℝ) ^ 20 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hq := ratio_pos hb
  have hr : ratio b ≤ 4 * (b : ℝ) ^ 32 := by unfold ratio; linarith
  have hh := Real.rpow_le_rpow hq.le hr (by norm_num : (0 : ℝ) ≤ 5 / 8)
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ b)] at hh
  have h4 : (4 : ℝ) ^ (5 / 8 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hbpow : (b : ℝ) ^ ((32 : ℝ) * (5 / 8)) ≤ (b : ℝ) ^ 20 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbR (by norm_num)
  exact hh.trans (mul_le_mul h4 hbpow (by positivity) (by norm_num))

lemma oracle_cost {T : ℝ} (hT : 0 ≤ T) :
    (recoveryCalls (base T ^ 20) (depth T) : ℝ) ≤
      8 * (33 * (1 + Real.log (2 + T))) ^ 20 * (2 + T) ^ (5 / 8 : ℝ) := by
  have hb := base_bounds hT
  have hb1 : 1 ≤ base T := by omega
  have hb2 : 2 ≤ base T := by omega
  have hq := ratio_pos hb1
  have hu : 0 < 2 + T := by linarith
  have hc := recovery_calls (show 1 ≤ base T ^ 20 from one_le_pow₀ hb1) (depth T)
  have hcR : (recoveryCalls (base T ^ 20) (depth T) : ℝ) ≤
      2 * (2 * (base T : ℝ) ^ 20) ^ depth T := by exact_mod_cast hc
  have hp := recursive_power hb2 (depth T)
  have hscale := (depth_scale hT).2
  have hr := Real.rpow_le_rpow (pow_pos hq _).le hscale (by norm_num : (0 : ℝ) ≤ 5 / 8)
  rw [Real.mul_rpow hq.le hu.le] at hr
  have hqr := ratio_power hb1
  have hupper := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ base T) hb.2.2 20
  have hqbound : ratio (base T) ^ (5 / 8 : ℝ) ≤ 4 * (33 * (1 + Real.log (2 + T))) ^ 20 :=
    hqr.trans (mul_le_mul_of_nonneg_left hupper (by norm_num))
  have hlast := mul_le_mul_of_nonneg_right hqbound (Real.rpow_nonneg hu.le (5 / 8 : ℝ))
  nlinarith only [hcR, hp, hr, hlast]

end LongTails.Proofs.SharpEnvelopeBudget
