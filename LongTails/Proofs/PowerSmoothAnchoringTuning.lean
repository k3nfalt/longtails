import LongTails.Algorithms.PowerSmoothAnchoring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace LongTails.Proofs.PowerSmoothAnchoringTuning

open LongTails.Setups.StochasticPowerSmoothFixedPoint
open LongTails.Algorithms.PowerSmoothAnchoring

lemma strength_pos (q : Params) (j : ℕ) : 0 < strength q j := by
  unfold strength
  positivity

lemma strength_double (q : Params) (j : ℕ) : strength q (j + 1) = 2 * strength q j := by
  simp only [strength, pow_succ]
  ring

lemma strength_last (q : Params) : strength q (levels q) = 1 := by
  simp [strength]

lemma relaxation_pos (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 < relaxation q := by
  unfold relaxation
  positivity

lemma relaxation_identity (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    relaxation q * (1 + (2 : ℝ) ^ levels q +
      (65536 * q.K * (q.σ / q.ε) ^ q.exponent * (levels q + 1 : ℝ) ^ q.exponent) ^
        (1 / (q.exponent - 1))) = 1 := by
  have hd : 0 < 1 + (2 : ℝ) ^ levels q +
      (65536 * q.K * (q.σ / q.ε) ^ q.exponent * (levels q + 1 : ℝ) ^ q.exponent) ^
        (1 / (q.exponent - 1)) := by positivity
  unfold relaxation
  exact div_mul_cancel₀ 1 hd.ne'

lemma relaxation_le_one (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    relaxation q ≤ 1 := by
  have hd := relaxation_identity q hK hσ hε
  have hr := (relaxation_pos q hK hσ hε).le
  have hp : 0 ≤ (2 : ℝ) ^ levels q := by positivity
  have hn : 0 ≤ (65536 * q.K * (q.σ / q.ε) ^ q.exponent *
      (levels q + 1 : ℝ) ^ q.exponent) ^ (1 / (q.exponent - 1)) := by positivity
  nlinarith [mul_nonneg hr hp, mul_nonneg hr hn]

lemma stageStep_nonneg (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) (j : ℕ) : 0 ≤ stageStep q j := by
  unfold stageStep
  exact div_nonneg (mul_nonneg (relaxation_pos q hK hσ hε).le
    (by linarith [strength_pos q j])) (strength_pos q j).le

lemma stageStep_le_one (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) (j : ℕ) : stageStep q j ≤ 1 := by
  have hd := relaxation_identity q hK hσ hε
  have hr := (relaxation_pos q hK hσ hε).le
  have hn : 0 ≤ (65536 * q.K * (q.σ / q.ε) ^ q.exponent *
      (levels q + 1 : ℝ) ^ q.exponent) ^ (1 / (q.exponent - 1)) := by positivity
  have hb : relaxation q * (1 + (2 : ℝ) ^ levels q) ≤ 1 := by
    nlinarith [mul_nonneg hr hn]
  have ha := strength_pos q j
  have hp : 1 ≤ strength q j * (2 : ℝ) ^ levels q := by
    have ht : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    simpa only [strength, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ levels q ≠ 0)] using ht
  unfold stageStep
  rw [div_le_iff₀ ha]
  nlinarith [mul_le_mul_of_nonneg_left hb ha.le, mul_le_mul_of_nonneg_left hp hr]

lemma stageStep_drift (q : Params) (j : ℕ) :
    stageStep q j * strength q j / (1 + strength q j) = relaxation q := by
  have ha := strength_pos q j
  unfold stageStep
  field_simp

lemma innerSteps_pos (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 < innerSteps q := by
  unfold innerSteps
  apply Nat.ceil_pos.mpr
  exact div_pos (by positivity) (relaxation_pos q hK hσ hε)

lemma innerSteps_contraction (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) : 8 * (levels q + 1 : ℝ) ≤ relaxation q * innerSteps q := by
  have h := Nat.le_ceil (8 * (levels q + 1 : ℝ) / relaxation q)
  rw [div_le_iff₀ (relaxation_pos q hK hσ hε)] at h
  simpa only [innerSteps, mul_comm] using h

lemma initial_strength_radius (q : Params) (hε : 0 < q.ε) :
    strength q 0 * q.D ≤ q.ε / 16 := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (⌈16 * q.D / q.ε⌉₊ + 1)
  have hc : (⌈16 * q.D / q.ε⌉₊ : ℝ) ≤ (2 : ℝ) ^ levels q := by
    have hn : ⌈16 * q.D / q.ε⌉₊ ≤ 2 ^ levels q := (Nat.le_succ _).trans hp
    exact_mod_cast hn
  have hr : 16 * q.D / q.ε ≤ (2 : ℝ) ^ levels q := (Nat.le_ceil _).trans hc
  rw [div_le_iff₀ hε] at hr
  simp only [strength, pow_zero]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  field_simp
  nlinarith

lemma normalized_noise_floor (q : Params) (hs : 1 < q.exponent) (hK : 0 ≤ q.K)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    q.K * relaxation q ^ (q.exponent - 1) * q.σ ^ q.exponent ≤
      q.ε ^ q.exponent / (65536 * (levels q + 1 : ℝ) ^ q.exponent) := by
  let B := 65536 * q.K * (q.σ / q.ε) ^ q.exponent * (levels q + 1 : ℝ) ^ q.exponent
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ht : 0 ≤ B ^ (1 / (q.exponent - 1)) := Real.rpow_nonneg hB _
  have hd := relaxation_identity q hK hσ hε
  have hr := (relaxation_pos q hK hσ hε).le
  have hb : relaxation q * B ^ (1 / (q.exponent - 1)) ≤ 1 := by
    change relaxation q * (1 + (2 : ℝ) ^ levels q + B ^ (1 / (q.exponent - 1))) = 1 at hd
    nlinarith [mul_nonneg hr (show 0 ≤ (2 : ℝ) ^ levels q by positivity)]
  have hp := Real.rpow_le_rpow (mul_nonneg hr ht) hb (show 0 ≤ q.exponent - 1 by linarith)
  rw [Real.mul_rpow hr ht, ← Real.rpow_mul hB,
    one_div_mul_cancel (by linarith : q.exponent - 1 ≠ 0), Real.rpow_one,
    Real.one_rpow] at hp
  have hεp : 0 < q.ε ^ q.exponent := Real.rpow_pos_of_pos hε _
  have hSp : 0 < (levels q + 1 : ℝ) ^ q.exponent := Real.rpow_pos_of_pos (by positivity) _
  dsimp [B] at hp
  rw [Real.div_rpow hσ hε.le] at hp
  have he : relaxation q ^ (q.exponent - 1) *
      (65536 * q.K * (q.σ ^ q.exponent / q.ε ^ q.exponent) *
        (levels q + 1 : ℝ) ^ q.exponent) =
      (q.K * relaxation q ^ (q.exponent - 1) * q.σ ^ q.exponent *
        (65536 * (levels q + 1 : ℝ) ^ q.exponent)) / q.ε ^ q.exponent := by ring
  rw [he, div_le_iff₀ hεp] at hp
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [one_mul] using hp

lemma contraction_decay (δ S : ℝ) (hδ1 : δ ≤ 1) (hS : 0 < S)
    (n : ℕ) (hn : 8 * S ≤ δ * n) :
    (1 - δ) ^ n ≤ 1 / (64 * S ^ 2) := by
  have hc : 1 - δ ≤ Real.exp (-δ) := by linarith [Real.add_one_le_exp (-δ)]
  have hexp : (1 - δ) ^ n ≤ Real.exp (-(8 * S)) := by
    calc
      _ ≤ Real.exp (-δ) ^ n := pow_le_pow_left₀ (by linarith) hc n
      _ = Real.exp ((n : ℝ) * (-δ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have he2 := Real.add_one_le_exp (2 * S)
  have h4 : 8 * S ≤ Real.exp (4 * S) := by
    have hp2 := (sq_le_sq₀ (by positivity : 0 ≤ 2 * S + 1)
      (Real.exp_nonneg (2 * S))).mpr he2
    have he4 : Real.exp (4 * S) = Real.exp (2 * S) ^ 2 := by
      rw [show 4 * S = 2 * S + 2 * S by ring, Real.exp_add]
      ring
    rw [he4]
    nlinarith [sq_nonneg (2 * S - 1)]
  have h8 : 64 * S ^ 2 ≤ Real.exp (8 * S) := by
    have hp4 := (sq_le_sq₀ (by positivity : 0 ≤ 8 * S)
      (Real.exp_nonneg (4 * S))).mpr h4
    have he8 : Real.exp (8 * S) = Real.exp (4 * S) ^ 2 := by
      rw [show 8 * S = 4 * S + 4 * S by ring, Real.exp_add]
      ring
    rw [he8]
    nlinarith
  apply hexp.trans
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h8

lemma innerSteps_decay (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    (1 - relaxation q) ^ innerSteps q ≤ 1 / (64 * (levels q + 1 : ℝ) ^ 2) :=
  contraction_decay _ _ (relaxation_le_one q hK hσ hε) (by positivity) _
    (innerSteps_contraction q hK hσ hε)

lemma bootstrap_noise {s ε S ν : ℝ} (hs2 : s ≤ 2)
    (hε : 0 < ε) (hS : 0 < S)
    (hν : ν ≤ ε ^ s / (65536 * S ^ s)) :
    ν ≤ (ε / (32 * S)) ^ s / 64 := by
  have hc : (32 : ℝ) ^ s ≤ 1024 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 32 by norm_num) hs2
    norm_num at this
    exact this
  have hp : 0 < S ^ s := Real.rpow_pos_of_pos hS _
  have h32 : 0 < (32 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  apply hν.trans
  rw [Real.div_rpow hε.le (by positivity), Real.mul_rpow (by norm_num) hS.le]
  rw [div_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

lemma bootstrap_initial {s ε S q : ℝ} (hs2 : s ≤ 2)
    (hε : 0 < ε) (hS : 1 ≤ S) (hq : q ≤ 1 / (64 * S ^ 2)) :
    q * (ε / 8) ^ s ≤ (ε / (32 * S)) ^ s / 4 := by
  have hSp : 0 < S := by linarith
  have hp : (4 * S) ^ s ≤ 16 * S ^ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 4 * S by linarith) hs2
    norm_num at hh
    nlinarith
  have he : (ε / 8) ^ s = (4 * S) ^ s * (ε / (32 * S)) ^ s := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (show 0 ≤ 4 * S by positivity) s)
  have hn : (1 / (64 * S ^ 2)) * (4 * S) ^ s ≤ 1 / 4 := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hc : q * (4 * S) ^ s ≤ 1 / 4 := hm.trans hn
  have hh := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg (show 0 ≤ ε / (32 * S) by positivity) s)
  nlinarith

lemma scaled_noise_identity (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) (j : ℕ) :
    q.K * (stageStep q j / (1 + strength q j)) ^ q.exponent *
      q.σ ^ q.exponent * strength q j ^ q.exponent =
      relaxation q * (q.K * relaxation q ^ (q.exponent - 1) * q.σ ^ q.exponent) := by
  have ha := strength_pos q j
  have hd := relaxation_pos q hK hσ hε
  have he : stageStep q j / (1 + strength q j) = relaxation q / strength q j := by
    unfold stageStep
    field_simp
  rw [he, Real.div_rpow hd.le ha.le, Real.rpow_sub hd, Real.rpow_one]
  have hp : strength q j ^ q.exponent ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  field_simp

lemma stationary_noise (q : Params) (hK : 0 ≤ q.K) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) (j : ℕ) :
    (1 - stageStep q j * strength q j / (1 + strength q j)) *
        (q.K * relaxation q ^ (q.exponent - 1) * q.σ ^ q.exponent) +
      q.K * (stageStep q j / (1 + strength q j)) ^ q.exponent *
        q.σ ^ q.exponent * strength q j ^ q.exponent =
      q.K * relaxation q ^ (q.exponent - 1) * q.σ ^ q.exponent := by
  rw [stageStep_drift, scaled_noise_identity q hK hσ hε]
  ring

lemma bootstrap_next {B V q S : ℝ} (hB : 0 ≤ B) (hS : 1 ≤ S)
    (hq : q ≤ 1 / (64 * S ^ 2)) (hV : V ≤ B / 64) : q * (9 * B) + V ≤ B := by
  have hc : q ≤ 1 / 64 := hq.trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith [sq_nonneg (S - 1)]))
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ 9 * B by positivity)
  nlinarith

end LongTails.Proofs.PowerSmoothAnchoringTuning
