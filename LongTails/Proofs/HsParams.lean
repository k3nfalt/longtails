import LongTails.Proofs.HsBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Complex.ExponentialBounds

open LongTails.Proofs.HsBounds

namespace LongTails.Proofs.HsParams

lemma cube_le_pow (m : ℕ) : (2 * m + 65) ^ 3 ≤ 2 ^ (m + 32) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h1 : (2 * (m + 1) + 65) ^ 3 ≤ 2 * (2 * m + 65) ^ 3 := by
      have : 2 * (m + 1) + 65 = (2 * m + 65) + 2 := by ring
      rw [this]
      nlinarith [Nat.zero_le m, sq_nonneg (2 * m + 65)]
    calc (2 * (m + 1) + 65) ^ 3 ≤ 2 * (2 * m + 65) ^ 3 := h1
      _ ≤ 2 * 2 ^ (m + 32) := by omega
      _ = 2 ^ (m + 1 + 32) := by ring

def pK (k : ℕ) : ℕ := 2 * (3 * Nat.clog 2 (k + 1) + 40) + 64

lemma pK_ge (k : ℕ) : 2 ≤ pK k := by unfold pK; omega

lemma pK_q (k : ℕ) :
    2 ^ 22 * ((pK k : ℝ) + 1) ^ 3 * KK k ^ 3 * (1 / 2) ^ pK k ≤ 8 := by
  set c := Nat.clog 2 (k + 1)
  set m := 3 * c + 40
  have hp : pK k = 2 * m + 64 := rfl
  have hcube := cube_le_pow m
  have hK : k + 1 ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have hK3 : (k + 1) ^ 3 ≤ 2 ^ (3 * c) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hK 3
  have hnat : 2 ^ 22 * (pK k + 1) ^ 3 * (k + 1) ^ 3 ≤ 8 * 2 ^ pK k := by
    rw [hp]
    have e1 : 2 * m + 64 + 1 = 2 * m + 65 := by ring
    rw [e1]
    calc 2 ^ 22 * (2 * m + 65) ^ 3 * (k + 1) ^ 3 ≤ 2 ^ 22 * 2 ^ (m + 32) * 2 ^ (3 * c) := by
          gcongr
      _ = 2 ^ (22 + (m + 32) + 3 * c) := by ring
      _ ≤ 2 ^ (3 + (2 * m + 64)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          omega
      _ = 8 * 2 ^ (2 * m + 64) := by rw [pow_add]; norm_num
  have hreal : (2 : ℝ) ^ 22 * ((pK k : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ^ 3 ≤ 8 * 2 ^ pK k := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < 2 ^ pK k := by positivity
  unfold KK
  rw [div_pow, one_pow]
  rw [show (2 : ℝ) ^ 22 * ((pK k : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ^ 3 * (1 / 2 ^ pK k) =
    (2 ^ 22 * ((pK k : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ^ 3) / 2 ^ pK k by ring]
  rw [div_le_iff₀ hpos]
  exact hreal

lemma six_c_le (c : ℕ) (hc : 11 ≤ c) : 6 * c + 145 ≤ 2 ^ (c - 1) := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
    have : 2 ^ (c + 1 - 1) = 2 * 2 ^ (c - 1) := by
      rw [show c + 1 - 1 = (c - 1) + 1 by omega, pow_succ]; ring
    rw [this]
    have : 1 ≤ 2 ^ (c - 1) := Nat.one_le_two_pow
    omega

lemma pK_le (k : ℕ) (hk : 1024 ≤ k) : pK k + 1 ≤ k + 1 := by
  set c := Nat.clog 2 (k + 1)
  have hlt : 2 ^ c.pred < k + 1 := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hle : k + 1 ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have hc : 11 ≤ c := by
    by_contra h
    push Not at h
    have : 2 ^ c ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h6 := six_c_le c hc
  have : c.pred = c - 1 := rfl
  rw [this] at hlt
  unfold pK
  omega

lemma clog_le_log (k : ℕ) (hk : 1 ≤ k) :
    (Nat.clog 2 (k + 1) : ℝ) ≤ Real.log ((k : ℝ) + 1) / Real.log 2 + 1 := by
  set c := Nat.clog 2 (k + 1)
  have hlt : 2 ^ c.pred < k + 1 := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hlt' : (2 : ℝ) ^ c.pred < (k : ℝ) + 1 := by exact_mod_cast hlt
  have hlog := Real.log_lt_log (by positivity) hlt'
  rw [Real.log_pow] at hlog
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcp : (c : ℝ) ≤ (c.pred : ℝ) + 1 := by
    have : c ≤ c.pred + 1 := by rw [Nat.pred_eq_sub_one]; omega
    exact_mod_cast this
  have : (c.pred : ℝ) ≤ Real.log ((k : ℝ) + 1) / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  linarith

section Budget

noncomputable def Lg (Y : ℝ) : ℝ := Real.log (2 + Y)

noncomputable def Xb (Y : ℝ) : ℝ := Y / (2 ^ 18 * Lg Y)

noncomputable def bud (Y : ℝ) : ℕ := ⌊Xb Y ^ ((2 : ℝ) / 3)⌋₊

variable {Y : ℝ}

lemma Lg_ge (hY : 2 ^ 60 ≤ Y) : 41 ≤ Lg Y := by
  unfold Lg
  have h1 : Real.log (2 ^ 60) ≤ Real.log (2 + Y) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_pow] at h1
  have h2 := Real.log_two_gt_d9
  push_cast at h1
  linarith

lemma Lg_le (hY : 2 ^ 60 ≤ Y) : Lg Y ≤ 8 * Y ^ ((1 : ℝ) / 4) := by
  have hY0 : 0 < Y := by linarith [show (0 : ℝ) < 2 ^ 60 by positivity]
  have h1 := Real.log_le_rpow_div (x := 2 + Y) (by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 : (2 + Y) ^ ((1 : ℝ) / 4) ≤ (2 * Y) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by linarith) (by linarith [show (2 : ℝ) ≤ 2 ^ 60 by norm_num])
      (by norm_num)
  have h3 : (2 * Y) ^ ((1 : ℝ) / 4) = 2 ^ ((1 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) :=
    Real.mul_rpow (by norm_num) hY0.le
  have h4 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h5 : 0 ≤ Y ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hY0.le _
  unfold Lg
  calc Real.log (2 + Y) ≤ (2 + Y) ^ ((1 : ℝ) / 4) / (1 / 4) := h1
    _ = 4 * (2 + Y) ^ ((1 : ℝ) / 4) := by ring
    _ ≤ 4 * (2 * Y ^ ((1 : ℝ) / 4)) := by
        rw [h3] at h2
        nlinarith
    _ = 8 * Y ^ ((1 : ℝ) / 4) := by ring

lemma Xb_ge (hY : 2 ^ 60 ≤ Y) : 2 ^ 24 ≤ Xb Y := by
  have hY0 : 0 < Y := by linarith [show (0 : ℝ) < 2 ^ 60 by positivity]
  have hL := Lg_le hY
  have hL0 : 0 < Lg Y := by linarith [Lg_ge hY]
  have hq : 0 < Y ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hY0 _
  have hsplit : Y = Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]; norm_num
  have h34 : (2 : ℝ) ^ 45 ≤ Y ^ ((3 : ℝ) / 4) := by
    have : ((2 : ℝ) ^ 60) ^ ((3 : ℝ) / 4) ≤ Y ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hY (by norm_num)
    have e : ((2 : ℝ) ^ 60) ^ ((3 : ℝ) / 4) = 2 ^ 45 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  unfold Xb
  rw [le_div_iff₀ (by positivity)]
  calc (2 : ℝ) ^ 24 * (2 ^ 18 * Lg Y) ≤ 2 ^ 24 * (2 ^ 18 * (8 * Y ^ ((1 : ℝ) / 4))) := by gcongr
    _ = 2 ^ 45 * Y ^ ((1 : ℝ) / 4) := by ring
    _ ≤ Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by gcongr
    _ = Y := by rw [mul_comm, ← hsplit]

lemma Xb_le (hY : 2 ^ 60 ≤ Y) : Xb Y ≤ Y / 2 ^ 18 := by
  have hY0 : 0 < Y := by linarith [show (0 : ℝ) < 2 ^ 60 by positivity]
  have hL := Lg_ge hY
  unfold Xb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma bud_le (hY : 2 ^ 60 ≤ Y) : (bud Y : ℝ) ≤ Xb Y ^ ((2 : ℝ) / 3) :=
  Nat.floor_le (Real.rpow_nonneg (by linarith [Xb_ge hY, show (0 : ℝ) < 2 ^ 24 by positivity]) _)

lemma bud_ge (hY : 2 ^ 60 ≤ Y) : 512 ≤ bud Y := by
  have hX := Xb_ge hY
  have h1 : ((2 : ℝ) ^ 24) ^ ((2 : ℝ) / 3) ≤ Xb Y ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hX (by norm_num)
  have e : ((2 : ℝ) ^ 24) ^ ((2 : ℝ) / 3) = 2 ^ 16 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e] at h1
  unfold bud
  apply Nat.le_floor
  push_cast
  linarith

lemma bud_cube (hY : 2 ^ 60 ≤ Y) : (bud Y : ℝ) ^ 3 ≤ Xb Y ^ 2 := by
  have hX0 : 0 ≤ Xb Y := by linarith [Xb_ge hY, show (0 : ℝ) < 2 ^ 24 by positivity]
  have h := pow_le_pow_left₀ (Nat.cast_nonneg _) (bud_le hY) 3
  have e : (Xb Y ^ ((2 : ℝ) / 3)) ^ 3 = Xb Y ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
  linarith

lemma bud_le_X (hY : 2 ^ 60 ≤ Y) : (bud Y : ℝ) ≤ Xb Y := by
  have hX := Xb_ge hY
  have h1 : Xb Y ^ ((2 : ℝ) / 3) ≤ Xb Y ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [show (1 : ℝ) ≤ 2 ^ 24 by norm_num])
      (by norm_num)
  rw [Real.rpow_one] at h1
  exact (bud_le hY).trans h1

lemma KK_bud_le (hY : 2 ^ 60 ≤ Y) : KK (2 * bud Y) ≤ 3 * (bud Y : ℝ) := by
  have h := bud_ge hY
  have h' : (512 : ℝ) ≤ bud Y := by exact_mod_cast h
  unfold KK
  push_cast
  linarith

lemma pK_le_log (hY : 2 ^ 60 ≤ Y) : (pK (2 * bud Y) : ℝ) + 1 ≤ 13 * Lg Y := by
  have hb := bud_ge hY
  have hc := clog_le_log (2 * bud Y) (by omega)
  have hK : ((2 * bud Y : ℕ) : ℝ) + 1 ≤ Y := by
    have h1 := KK_bud_le hY
    have h2 := bud_le_X hY
    have h3 := Xb_le hY
    unfold KK at h1
    have : 3 * Xb Y ≤ Y := by
      have : Y / 2 ^ 18 * 3 ≤ Y := by
        have hY0 : 0 < Y := by linarith [show (0 : ℝ) < 2 ^ 60 by positivity]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
      linarith
    linarith
  have hlogK : Real.log (((2 * bud Y : ℕ) : ℝ) + 1) ≤ Lg Y := by
    unfold Lg
    exact Real.log_le_log (by positivity) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hdiv : Real.log (((2 * bud Y : ℕ) : ℝ) + 1) / Real.log 2 ≤ Lg Y / (69 / 100) := by
    apply div_le_div₀ (by linarith [Lg_ge hY]) hlogK (by norm_num) (by linarith)
  have hL := Lg_ge hY
  unfold pK
  push_cast
  have : (Nat.clog 2 (2 * bud Y + 1) : ℝ) ≤ Lg Y / (69 / 100) + 1 := by
    linarith
  nlinarith

end Budget

section Constants

variable {k p : ℕ}

lemma cS_le_amgm : cS k p ≤ (KK k + 32 * ((p : ℝ) + 1)) / 2 := by
  have h := cS_sq (k := k) p
  have h0 := (cS_pos (k := k) p).le
  have hK := KK_pos k
  have hsq : cS k p ^ 2 ≤ ((KK k + 32 * ((p : ℝ) + 1)) / 2) ^ 2 := by
    rw [h]; nlinarith [sq_nonneg (KK k - 32 * ((p : ℝ) + 1))]
  have hr : 0 ≤ (KK k + 32 * ((p : ℝ) + 1)) / 2 := by positivity
  nlinarith [sq_nonneg (cS k p - (KK k + 32 * ((p : ℝ) + 1)) / 2)]

lemma cM_le (hpK : (p : ℝ) + 1 ≤ KK k) : cM k p ≤ 1500 * ((p : ℝ) + 1) * KK k := by
  have hS := cS_le_amgm (k := k) (p := p)
  have hS0 := (cS_pos (k := k) p).le
  have hK := KK_ge k
  set K := KK k
  set P := (p : ℝ) + 1 with hP
  have hP1 : 1 ≤ P := by rw [hP]; have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith
  have hch : ch k = 1 / (8 * K) := rfl
  have hcw : cw = 1 / 8 := rfl
  have hcκ : cκ = 4 := rfl
  have e : cM k p = 64 * (p : ℝ) * K + (14 * K + 9) * (32 * P) + cS k p * (32 * P) +
      4 * (32 * P) + 1 + cS k p := by
    unfold cM
    rw [hch, hcw, hcκ, ← hP]
    have hKp : 0 < K := by linarith
    field_simp
    ring
  rw [e]
  have hp : (p : ℝ) ≤ P := by rw [hP]; linarith
  have h1 : cS k p * (32 * P) ≤ (K + 32 * P) / 2 * (32 * P) :=
    mul_le_mul_of_nonneg_right hS (by positivity)
  have hPK : P * P ≤ P * K := mul_le_mul_of_nonneg_left hpK (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 64 * K by positivity)]

end Constants

end LongTails.Proofs.HsParams
