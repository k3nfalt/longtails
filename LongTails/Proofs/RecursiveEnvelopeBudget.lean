import LongTails.Algorithms.RecursiveEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.RecursiveEnvelopeBudget

open LongTails.Algorithms.RecursiveEnvelope

noncomputable def depth (T : ℝ) : ℕ := ⌈Real.sqrt (Real.log (2 + T) / Real.log 4)⌉₊

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  linarith

lemma depth_bounds {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ depth T ∧ Real.sqrt (Real.log (2 + T) / Real.log 4) ≤ (depth T : ℝ) ∧
      (depth T : ℝ) ≤ Real.sqrt (Real.log (2 + T) / Real.log 4) + 1 := by
  have hl : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  have hf : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hs : 0 < Real.sqrt (Real.log (2 + T) / Real.log 4) := Real.sqrt_pos.2 (div_pos hl hf)
  refine ⟨?_, Nat.le_ceil _, (Nat.ceil_lt_add_one hs.le).le⟩
  unfold depth
  exact Nat.one_le_ceil_iff.mpr hs

lemma depth_scale {T : ℝ} (hT : 0 ≤ T) : T ≤ ((4 : ℝ) ^ depth T) ^ depth T := by
  obtain ⟨_, hd, _⟩ := depth_bounds hT
  have hl : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hf : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hs := Real.sq_sqrt (div_nonneg hl hf.le)
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hd 2
  have hh : Real.log (2 + T) ≤ (depth T : ℝ) ^ 2 * Real.log 4 := by
    rw [hs, div_le_iff₀ hf] at hsq
    exact hsq
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log (by linarith : 0 < 2 + T)] at he
  have hid : Real.exp ((depth T : ℝ) ^ 2 * Real.log 4) = ((4 : ℝ) ^ depth T) ^ depth T := by
    rw [pow_two, mul_assoc, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hid] at he
  linarith

lemma depth_simple {T : ℝ} (hT : 0 ≤ T) :
    (depth T : ℝ) ≤ Real.sqrt (Real.log (2 + T)) + 1 := by
  have hf : 1 ≤ Real.log 4 := by rw [log_four]; linarith [Real.log_two_gt_d9]
  have hl : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hh : Real.log (2 + T) / Real.log 4 ≤ Real.log (2 + T) :=
    div_le_self hl hf
  exact (depth_bounds hT).2.2.trans (add_le_add (Real.sqrt_le_sqrt hh) le_rfl)

lemma public_noise {T α : ℝ} (hT : 0 ≤ T)
    (hα : α ≤ Real.exp (-8 * (1 + Real.sqrt (Real.log (2 + T)))) / 100) :
    α ≤ levelError (depth T) 0 := by
  have hd := depth_simple hT
  have hl : Real.log 64 ≤ 8 := by
    have hh : Real.log 64 = 6 * Real.log 2 := by
      have he := Real.log_pow (2 : ℝ) 6
      norm_num at he
      linarith
    rw [hh]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl0 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul hd hl hl0 (by positivity : 0 ≤ Real.sqrt (Real.log (2 + T)) + 1)
  have he := Real.exp_le_exp.mpr (show -8 * (1 + Real.sqrt (Real.log (2 + T))) ≤
      -((depth T : ℝ) * Real.log 64) by nlinarith)
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 64)] at he
  have hh := div_le_div_of_nonneg_right he (by norm_num : (0 : ℝ) ≤ 100)
  apply hα.trans
  convert hh using 1
  simp only [levelError, pow_zero]
  field_simp

lemma calls_le {m : ℕ} (hm : 2 ≤ m) (d : ℕ) : calls m d ≤ 2 * m ^ d := by
  induction d with
  | zero => simp [calls]
  | succ d ih =>
      rw [calls, pow_succ]
      have hh := Nat.mul_le_mul_left (m ^ d) hm
      nlinarith

lemma depth_quadratic {T : ℝ} (hT : 0 ≤ T) :
    (depth T : ℝ) ^ 2 * Real.log 2 ≤
      Real.log (2 + T) / 2 + 2 * Real.sqrt (Real.log (2 + T)) + 1 := by
  let a := Real.sqrt (Real.log (2 + T) / Real.log 4)
  let s := Real.sqrt (Real.log (2 + T))
  have hl : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hf : 1 ≤ Real.log 4 := by rw [log_four]; linarith [Real.log_two_gt_d9]
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have has : a ≤ s := Real.sqrt_le_sqrt (div_le_self hl hf)
  have haa : a ^ 2 * Real.log 4 = Real.log (2 + T) := by
    rw [show a ^ 2 = Real.log (2 + T) / Real.log 4 from Real.sq_sqrt (by positivity)]
    exact div_mul_cancel₀ _ (by linarith)
  rw [log_four] at haa
  have hd := (depth_bounds hT).2.2
  change (depth T : ℝ) ≤ a + 1 at hd
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (depth T : ℝ)) hd 2
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_right hsq hl2
  have hx := mul_le_mul_of_nonneg_left hl21 (by positivity : 0 ≤ 2 * a + 1)
  change _ ≤ Real.log (2 + T) / 2 + 2 * s + 1
  nlinarith

lemma oracle_cost {T : ℝ} (hT : 0 ≤ T) :
    (calls (2048 * depth T * 2 ^ depth T) (depth T) : ℝ) ≤
      4 * Real.sqrt (2 + T) * Real.exp (32 * (1 + Real.sqrt (Real.log (2 + T))) *
        Real.log (32 + Real.log (2 + T))) := by
  let d := depth T
  let m := 2048 * d * 2 ^ d
  let s := Real.sqrt (Real.log (2 + T))
  let H := Real.log (32 + Real.log (2 + T))
  have hd : 1 ≤ d := (depth_bounds hT).1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : 2 ≤ m := by
    have hp : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    dsimp [m]
    nlinarith
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = Real.log (2 + T) := Real.sq_sqrt hlog
  have hds : (d : ℝ) ≤ s + 1 := depth_simple hT
  have hH : 1 ≤ H := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ 32 + Real.log (2 + T) by linarith)
    rw [log_four] at hh
    dsimp [H]
    linarith [Real.log_two_gt_d9]
  have hdH : Real.log (d : ℝ) ≤ H := by
    apply Real.log_le_log (by positivity)
    dsimp [H] at hH
    nlinarith [sq_nonneg (s - 1)]
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlm : Real.log (m : ℝ) = 11 * Real.log 2 + Real.log (d : ℝ) + (d : ℝ) * Real.log 2 := by
    have hc : Real.log 2048 = 11 * Real.log 2 := by
      have hh := Real.log_pow (2 : ℝ) 11
      norm_num at hh
      linarith
    simp only [m, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), hc, Real.log_pow]
  have hq := depth_quadratic hT
  change (d : ℝ) ^ 2 * Real.log 2 ≤ Real.log (2 + T) / 2 + 2 * s + 1 at hq
  have h1 := mul_le_mul_of_nonneg_left hdH (by positivity : 0 ≤ (d : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ 11 * (d : ℝ))
  have h3 := mul_le_mul_of_nonneg_right hds (by linarith : 0 ≤ H)
  have h4 := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 14 * (s + 1))
  have hexponent : (d : ℝ) * Real.log (m : ℝ) ≤
      Real.log (2 + T) / 2 + 32 * (1 + s) * H := by
    rw [hlm]
    nlinarith
  have he := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_nat_mul, Real.exp_log hmR, Real.exp_add, Real.exp_half,
    Real.exp_log (by linarith : 0 < 2 + T)] at he
  have hc : (calls m d : ℝ) ≤ 2 * (m : ℝ) ^ d := by exact_mod_cast calls_le hm d
  change (calls m d : ℝ) ≤ 4 * Real.sqrt (2 + T) * Real.exp (32 * (1 + s) * H)
  have hp : 0 ≤ Real.sqrt (2 + T) * Real.exp (32 * (1 + s) * H) := by positivity
  nlinarith

end LongTails.Proofs.RecursiveEnvelopeBudget
