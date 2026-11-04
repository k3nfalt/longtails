import LongTails.Proofs.SharpDistanceParameters
import LongTails.Proofs.SharpEnvelopeBudget

namespace LongTails.Proofs.SharpDistanceBudget

open LongTails.Algorithms.SharpEnvelope SharpEnvelopeParameters SharpEnvelopeBudget
open SharpDistanceParameters

lemma iterations_bounds {b : ℕ} (hb : 1 ≤ b) :
    1 ≤ iterations b ∧ (2 * iterations b : ℕ) ≤ 16384 * (b : ℝ) ^ 16 * (1 + Real.log b) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hl : 0 ≤ Real.log b := Real.log_nonneg hbR
  have hp : (1 : ℝ) ≤ (b : ℝ) ^ 16 := one_le_pow₀ hbR
  have hprod : 1 ≤ (b : ℝ) ^ 16 * (1 + Real.log b) := by nlinarith
  have hc : 4096 * (b : ℝ) ^ 16 * (1 + Real.log b) ≤ iterations b := Nat.le_ceil _
  have hu : (iterations b : ℝ) < 4096 * (b : ℝ) ^ 16 * (1 + Real.log b) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  constructor
  · have : (1 : ℝ) ≤ iterations b := by nlinarith
    exact_mod_cast this
  · push_cast
    nlinarith

lemma depth_log_bound {T : ℝ} (hT : 0 ≤ T) :
    (depth T : ℝ) ≤ Real.log (2 + T) / (32 * Real.log (base T)) + 1 := by
  have hb := base_bounds hT
  have hbR : (1 : ℝ) < base T := by exact_mod_cast (show 1 < base T by omega)
  have hb0 : (0 : ℝ) < base T := by linarith
  have hp : (1 : ℝ) ≤ (base T : ℝ) ^ 32 := one_le_pow₀ hbR.le
  have hq := ratio_pos (by omega : 1 ≤ base T)
  have hqlo : (base T : ℝ) ^ 32 ≤ ratio (base T) := by unfold ratio; linarith
  have hl := Real.log_le_log (pow_pos hb0 32) hqlo
  rw [Real.log_pow] at hl
  norm_num at hl
  have hden : 0 < 32 * Real.log (base T) := mul_pos (by norm_num) (Real.log_pos hbR)
  have hu : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  have hdiv := div_le_div_of_nonneg_left hu.le hden hl
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.log (2 + T) / Real.log (ratio (base T)) from
    div_nonneg hu.le (by linarith))
  change (⌈Real.log (2 + T) / Real.log (ratio (base T))⌉₊ : ℝ) ≤ _
  linarith

lemma recursive_power {b m T : ℝ} {d : ℕ} (hb : 1 < b) (hm : 1 ≤ m) (hT : 0 ≤ T)
    (hphase : m ≤ 16384 * b ^ 16 * (1 + Real.log b))
    (hdepth : (d : ℝ) ≤ Real.log (2 + T) / (32 * Real.log b) + 1) :
    m ^ d ≤ 16384 * b ^ 16 * (1 + Real.log b) *
      (2 + T) ^ (1 / 2 + Real.log (16384 * (1 + Real.log b)) / (32 * Real.log b)) := by
  have hb0 : 0 < b := by linarith
  have hm0 : 0 < m := by linarith
  have hu : 0 < 2 + T := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlogu : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hM : 0 < 16384 * (1 + Real.log b) := by positivity
  have hphase' : m ≤ (16384 * (1 + Real.log b)) * b ^ 16 := by nlinarith only [hphase]
  have hl := Real.log_le_log hm0 hphase'
  rw [Real.log_mul hM.ne' (pow_pos hb0 16).ne', Real.log_pow] at hl
  norm_num at hl
  have hh := mul_le_mul hdepth hl hlogm
    (show 0 ≤ Real.log (2 + T) / (32 * Real.log b) + 1 by positivity)
  apply (Real.log_le_log_iff (pow_pos hm0 d) (by positivity)).mp
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_rpow hu]
  have he : Real.log (16384 * b ^ 16 * (1 + Real.log b)) =
      Real.log (16384 * (1 + Real.log b)) + 16 * Real.log b := by
    rw [show 16384 * b ^ 16 * (1 + Real.log b) = (16384 * (1 + Real.log b)) * b ^ 16 by ring,
      Real.log_mul hM.ne' (pow_pos hb0 16).ne', Real.log_pow]
    norm_num
  rw [he]
  have halgebra : (Real.log (2 + T) / (32 * Real.log b) + 1) *
      (Real.log (16384 * (1 + Real.log b)) + 16 * Real.log b) =
      (Real.log (16384 * (1 + Real.log b)) + 16 * Real.log b) +
        (1 / 2 + Real.log (16384 * (1 + Real.log b)) / (32 * Real.log b)) * Real.log (2 + T) := by
    field_simp
    ring
  rw [halgebra] at hh
  exact hh

lemma oracle_cost {T : ℝ} (hT : 0 ≤ T) :
    (recoveryCalls (iterations (base T)) (depth T) : ℝ) ≤
      32768 * (33 * (1 + Real.log (2 + T))) ^ 16 * (1 + Real.log (33 * (1 + Real.log (2 + T)))) *
        (2 + T) ^ (1 / 2 + Real.log (16384 * (1 + Real.log (33 * (1 + Real.log (2 + T))))) /
          (32 * Real.log (32 * (1 + Real.log (2 + T))))) := by
  let B := 33 * (1 + Real.log (2 + T))
  let A := 32 * (1 + Real.log (2 + T))
  have hb := base_bounds hT
  have hb1 : 1 ≤ base T := by omega
  have hbR : (1 : ℝ) < base T := by exact_mod_cast (show 1 < base T by omega)
  have hlu : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hA : 1 < A := by dsimp [A]; linarith
  have hB : 1 < B := by dsimp [B]; linarith
  have hAl : A ≤ base T := hb.2.1
  have hBu : (base T : ℝ) ≤ B := hb.2.2
  have hn := iterations_bounds hb1
  have hm : (1 : ℝ) ≤ (2 * iterations (base T) : ℕ) := by exact_mod_cast (show 1 ≤ 2 * iterations (base T) by omega)
  have hc := recovery_calls hn.1 (depth T)
  have hcR : (recoveryCalls (iterations (base T)) (depth T) : ℝ) ≤
      2 * ((2 * iterations (base T) : ℕ) : ℝ) ^ depth T := by exact_mod_cast hc
  have hp := recursive_power hbR hm hT hn.2 (depth_log_bound hT)
  have hlogb : 0 ≤ Real.log (base T) := Real.log_nonneg hbR.le
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB.le
  have hlower := Real.log_le_log (by linarith : 0 < A) hAl
  have hupper := Real.log_le_log (by linarith : (0 : ℝ) < base T) hBu
  have hnum := Real.log_le_log
    (show 0 < 16384 * (1 + Real.log (base T)) by positivity)
    (show 16384 * (1 + Real.log (base T)) ≤ 16384 * (1 + Real.log B) by linarith)
  have hnum0 : 0 ≤ Real.log (16384 * (1 + Real.log B)) := Real.log_nonneg (by linarith)
  have hden : 0 < 32 * Real.log (base T) := mul_pos (by norm_num) (Real.log_pos hbR)
  have hdenA : 0 < 32 * Real.log A := mul_pos (by norm_num) (Real.log_pos hA)
  have hfrac : Real.log (16384 * (1 + Real.log (base T))) / (32 * Real.log (base T)) ≤
      Real.log (16384 * (1 + Real.log B)) / (32 * Real.log A) := by
    exact (div_le_div_of_nonneg_right hnum hden.le).trans
      (div_le_div_of_nonneg_left hnum0 hdenA (by linarith))
  have hr := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 2 + T by linarith)
    (show 1 / 2 + Real.log (16384 * (1 + Real.log (base T))) / (32 * Real.log (base T)) ≤
      1 / 2 + Real.log (16384 * (1 + Real.log B)) / (32 * Real.log A) by linarith)
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ base T) hBu 16
  have hf := mul_le_mul hpow (show 1 + Real.log (base T) ≤ 1 + Real.log B by linarith)
    (by positivity : 0 ≤ 1 + Real.log (base T)) (pow_nonneg (by linarith : 0 ≤ B) 16)
  have hf' : 16384 * (base T : ℝ) ^ 16 * (1 + Real.log (base T)) ≤
      16384 * B ^ 16 * (1 + Real.log B) := by nlinarith only [hf]
  have hall := mul_le_mul hf' hr (by positivity) (by positivity)
  change _ ≤ 32768 * B ^ 16 * (1 + Real.log B) *
    (2 + T) ^ (1 / 2 + Real.log (16384 * (1 + Real.log B)) / (32 * Real.log A))
  nlinarith only [hcR, hp, hall]

end LongTails.Proofs.SharpDistanceBudget
