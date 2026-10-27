import LongTails.Proofs.SmoothBanachTuning
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.SmoothBanachBudget

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open SmoothBanachTuning

lemma ceil_clog_power_bound (x : ℝ) (hx : 0 ≤ x) :
    (2 : ℝ) ^ Nat.clog 2 (⌈x⌉₊ + 1) ≤ 2 * x + 4 := by
  let m := Nat.clog 2 (⌈x⌉₊ + 1)
  by_cases hm : m = 0
  · simp only [← show m = Nat.clog 2 (⌈x⌉₊ + 1) from rfl, hm, pow_zero]
    linarith
  · have hn : 1 < ⌈x⌉₊ + 1 := by
      by_contra hn
      have hz : ⌈x⌉₊ + 1 ≤ 1 := by omega
      exact hm (Nat.clog_of_right_le_one hz 2)
    have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : ℕ)) hn
    have hpR : (2 : ℝ) ^ (m - 1) < (⌈x⌉₊ : ℝ) + 1 := by exact_mod_cast hp
    have he : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ m)]
      rw [pow_succ, mul_comm]
    have hc := Nat.ceil_lt_add_one hx
    change (2 : ℝ) ^ m ≤ _
    rw [he]
    linarith

lemma levels_power_bound (q : Params) (hR : 0 ≤ q.R) (hε : 0 < q.ε) :
    (2 : ℝ) ^ levels q ≤ 32 * q.R / q.ε + 4 := by
  simpa only [levels, mul_div_assoc, ← mul_assoc, show (2 : ℝ) * 16 = 32 by norm_num] using
    ceil_clog_power_bound (16 * q.R / q.ε) (by positivity)

lemma levels_log_bound (q : Params) (hR : 0 ≤ q.R) (hε : 0 < q.ε) :
    (levels q + 1 : ℝ) ≤ 3 * (1 + Real.log (1 + 16 * q.R / q.ε)) := by
  let x := 16 * q.R / q.ε
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hp := ceil_clog_power_bound x hx
  have hp' : (2 : ℝ) ^ levels q ≤ 4 * (1 + x) := by
    change (2 : ℝ) ^ levels q ≤ 2 * x + 4 at hp
    linarith
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ levels q) hp'
  rw [Real.log_pow, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity)] at hl
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hl
  have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm : (0 : ℝ) ≤ levels q := Nat.cast_nonneg _
  by_cases hs : (levels q : ℝ) ≤ 2
  · change (levels q : ℝ) + 1 ≤ 3 * (1 + Real.log (1 + x))
    linarith
  · have hmul := mul_le_mul_of_nonneg_left htwo (by linarith : 0 ≤ (levels q : ℝ) - 2)
    change (levels q : ℝ) + 1 ≤ 3 * (1 + Real.log (1 + x))
    nlinarith

lemma execution_cost_bound (q : Params) (hC : 0 ≤ q.C) (hR : 0 ≤ q.R) (hε : 0 < q.ε) :
    ((levels q + 1) * innerSteps q : ℝ) ≤
      8192 * (1 + q.R / q.ε + q.C * q.σ ^ 2 / q.ε ^ 2) * (levels q + 1 : ℝ) ^ 4 := by
  let S : ℝ := levels q + 1
  let t := q.R / q.ε
  let v := q.C * q.σ ^ 2 / q.ε ^ 2
  have hS : 1 ≤ S := by dsimp [S]; linarith [Nat.cast_nonneg (α := ℝ) (levels q)]
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hδ := relaxation_pos q hC
  have hN := (Nat.ceil_lt_add_one (show 0 ≤ 8 * S / relaxation q by positivity)).le
  change (innerSteps q : ℝ) ≤ 8 * S / relaxation q + 1 at hN
  have hid : 8 * S / relaxation q + 1 =
      8 * S * (1 + (2 : ℝ) ^ levels q + 1024 * v * S ^ 2) + 1 := by
    dsimp [relaxation, v, S]
    field_simp
  rw [hid] at hN
  have hp := levels_power_bound q hR hε
  simp only [mul_div_assoc] at hp
  have hN' : (innerSteps q : ℝ) ≤ 8 * S * (5 + 32 * t + 1024 * v * S ^ 2) + 1 := by
    apply hN.trans
    dsimp [t]
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * S)]
  have hcost := mul_le_mul_of_nonneg_left hN' (by positivity : 0 ≤ S)
  have hS2 : S ^ 2 ≤ S ^ 4 := by nlinarith [sq_nonneg (S ^ 2 - 1)]
  have hS4 : S ≤ S ^ 4 := by nlinarith [sq_nonneg (S - 1)]
  have hdet := mul_le_mul_of_nonneg_right hS2 (by positivity : 0 ≤ 8 * (5 + 32 * t))
  have htS : 0 ≤ t * S ^ 4 := by positivity
  change S * (innerSteps q : ℝ) ≤ 8192 * (1 + t + v) * S ^ 4
  nlinarith

lemma public_cost_bound (q : Params) (hC : 0 ≤ q.C) (hR : 0 ≤ q.R) (hε : 0 < q.ε) :
    (levels q + 1) * innerSteps q ≤
      ⌈(2 : ℝ) ^ 20 * (1 + q.R / q.ε + q.C * q.σ ^ 2 / q.ε ^ 2) *
        (1 + Real.log (1 + 16 * q.R / q.ε)) ^ 4⌉₊ := by
  have hc := execution_cost_bound q hC hR hε
  have hl := levels_log_bound q hR hε
  have hL : 0 ≤ 1 + Real.log (1 + 16 * q.R / q.ε) := by
    have hh : 0 ≤ Real.log (1 + 16 * q.R / q.ε) := Real.log_nonneg (by
      have hh : 0 ≤ 16 * q.R / q.ε := by positivity
      linarith)
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (levels q + 1 : ℝ)) hl 4
  have hA : 0 ≤ 1 + q.R / q.ε + q.C * q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8192) hA)
  have hb : ((levels q + 1) * innerSteps q : ℝ) ≤
      (2 : ℝ) ^ 20 * (1 + q.R / q.ε + q.C * q.σ ^ 2 / q.ε ^ 2) *
        (1 + Real.log (1 + 16 * q.R / q.ε)) ^ 4 := by
    have hn := mul_nonneg hA (pow_nonneg hL 4)
    nlinarith
  exact_mod_cast hb.trans (Nat.le_ceil _)

end LongTails.Proofs.SmoothBanachBudget
