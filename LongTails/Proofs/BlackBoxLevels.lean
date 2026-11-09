import LongTails.Proofs.BlackBoxMacro
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

open OracleTemplate.OnlineMetricAccelerated (secant_bounds)

variable {d : ℕ}

noncomputable def jstar (μ : ℝ) : ℕ := ⌈Real.logb 2 (1 / μ)⌉₊

noncomputable def θc (w : Fin d → ℝ) : Fin d → ℝ := fun k => Real.log (w k) + Real.log 2

lemma one_le_two_pow_jstar {μ : ℝ} (hμ : 0 < μ) : 1 ≤ μ * 2 ^ jstar μ := by
  have h1 : Real.logb 2 (1 / μ) ≤ jstar μ := Nat.le_ceil _
  have h2 : (2 : ℝ) ^ Real.logb 2 (1 / μ) ≤ (2 : ℝ) ^ (jstar μ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at h2
  rw [div_le_iff₀ hμ] at h2
  linarith

lemma two_pow_jstar_le {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) : (2 : ℝ) ^ jstar μ ≤ 2 / μ := by
  have h0 : 0 ≤ Real.logb 2 (1 / μ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hμ]; linarith)
  have h1 : (jstar μ : ℝ) ≤ Real.logb 2 (1 / μ) + 1 := (Nat.ceil_lt_add_one h0).le
  have h2 : (2 : ℝ) ^ (jstar μ : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (1 / μ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
    Real.rpow_one, Real.rpow_natCast] at h2
  rw [show (1 : ℝ) / μ * 2 = 2 / μ by ring] at h2
  exact h2

lemma lt_jstar_of_invalid {μ : ℝ} (hμ : 0 < μ) {j : ℕ} (h : μ * 2 ^ j < 1) : j < jstar μ := by
  by_contra hc
  push Not at hc
  have := one_le_two_pow_jstar hμ
  have : (2 : ℝ) ^ jstar μ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hc
  nlinarith

section Facts

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ : ℝ} (Hy : BHyp f w μ) (x0 : Vec d)
include Hy

lemma sec_bounds (k : Fin d) : μ * w k ≤ sec f x0 k ∧ sec f x0 k ≤ w k :=
  secant_bounds Hy.smooth Hy.sc x0 k

lemma sec_pos (k : Fin d) : 0 < sec f x0 k :=
  lt_of_lt_of_le (mul_pos Hy.μ_pos (Hy.w_pos k)) (sec_bounds Hy x0 k).1

lemma θc_lo (k : Fin d) : lo (sec f x0) k ≤ θc w k := by
  unfold lo θc
  have := Real.log_le_log (sec_pos Hy x0 k) (sec_bounds Hy x0 k).2
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

lemma log_w_le {j : ℕ} (hj : 1 ≤ μ * 2 ^ j) (k : Fin d) :
    Real.log (w k) ≤ Real.log (sec f x0 k) + j * Real.log 2 := by
  have hs := sec_pos Hy x0 k
  have hb := (sec_bounds Hy x0 k).1
  have hw : w k ≤ sec f x0 k * 2 ^ j := by
    have hwpos := Hy.w_pos k
    calc w k = w k * 1 := (mul_one _).symm
      _ ≤ w k * (μ * 2 ^ j) := mul_le_mul_of_nonneg_left hj hwpos.le
      _ = μ * w k * 2 ^ j := by ring
      _ ≤ sec f x0 k * 2 ^ j := mul_le_mul_of_nonneg_right hb (by positivity)
  have := Real.log_le_log (Hy.w_pos k) hw
  rw [Real.log_mul hs.ne' (by positivity), Real.log_pow] at this
  linarith

lemma θc_hi {j : ℕ} (hj : 1 ≤ μ * 2 ^ j) (k : Fin d) : θc w k ≤ hi (sec f x0) j k := by
  unfold θc hi
  have := log_w_le Hy x0 hj k
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

omit Hy in
lemma th0_box (j : ℕ) (k : Fin d) :
    lo (sec f x0) k ≤ th0 (sec f x0) j k ∧ th0 (sec f x0) j k ≤ hi (sec f x0) j k := by
  unfold lo th0 hi
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> nlinarith

lemma th0_pot {j : ℕ} (hj : 1 ≤ μ * 2 ^ j) :
    sqn (fun k => th0 (sec f x0) j k - θc w k) ≤ d * (j * Real.log 2) ^ 2 / 4 := by
  have hpt : ∀ k, (th0 (sec f x0) j k - θc w k) ^ 2 ≤ (j * Real.log 2) ^ 2 / 4 := by
    intro k
    have h1 := log_w_le Hy x0 hj k
    have h2 := Real.log_le_log (sec_pos Hy x0 k) (sec_bounds Hy x0 k).2
    unfold th0 θc
    have : (Real.log (sec f x0 k) + Real.log 2 + j * Real.log 2 / 2 -
        (Real.log (w k) + Real.log 2)) ^ 2 ≤ (j * Real.log 2 / 2) ^ 2 := by
      apply sq_le_sq'
      · linarith
      · linarith
    nlinarith
  unfold sqn
  calc ∑ k, (th0 (sec f x0) j k - θc w k) ^ 2 ≤ ∑ _k : Fin d, (j * Real.log 2) ^ 2 / 4 :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = d * (j * Real.log 2) ^ 2 / 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma box_metric {θ : Fin d → ℝ} {j : ℕ}
    (hb : ∀ k, lo (sec f x0) k ≤ θ k ∧ θ k ≤ hi (sec f x0) j k) (k : Fin d) :
    sec f x0 k ≤ metric θ k ∧ metric θ k ≤ 4 * 2 ^ j * sec f x0 k := by
  have hs := sec_pos Hy x0 k
  unfold metric
  constructor
  · calc sec f x0 k = Real.exp (Real.log (sec f x0 k)) := (Real.exp_log hs).symm
      _ ≤ Real.exp (θ k) := Real.exp_le_exp.mpr (hb k).1
  · calc Real.exp (θ k) ≤ Real.exp (hi (sec f x0) j k) := Real.exp_le_exp.mpr (hb k).2
      _ = 4 * 2 ^ j * sec f x0 k := by
        unfold hi
        rw [Real.exp_add, Real.exp_add, Real.exp_log hs, Real.exp_log (by norm_num),
          show (j : ℝ) * Real.log 2 = Real.log (2 ^ j) by rw [Real.log_pow],
          Real.exp_log (by positivity)]
        ring

end Facts

end OracleTemplate.BlackBoxDiagonal
