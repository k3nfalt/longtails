import LongTails.Proofs.QuasarHardAdmissible
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseHardOracle

open QuasarCoinLaw QuasarHardAdmissible

noncomputable def coinError (p : ℝ) (b : Bool) : ℝ := if b then 1 / p - 1 else -1

noncomputable def oracleValue {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ) (g h : E → E) (x : E) (b : Bool) : E := g x + coinError p b • h x

lemma coinError_mean {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ b, coinError p b ∂(coinLaw p hp.le hp1 : Measure Bool)) = 0 := by
  rw [coin_integral]
  simp only [coinError, Bool.false_eq_true, ite_false, ite_true, smul_eq_mul]
  field_simp
  ring

lemma coinError_second {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ b, coinError p b ^ 2 ∂(coinLaw p hp.le hp1 : Measure Bool)) = (1 - p) / p := by
  rw [coin_integral]
  simp only [coinError, Bool.false_eq_true, ite_false, ite_true, smul_eq_mul]
  field_simp
  ring

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma oracle_unbiased {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (g h : E → E) (x : E) :
    ∫ b, oracleValue p g h x b ∂(coinLaw p hp.le hp1 : Measure Bool) = g x := by
  rw [coin_integral]
  simp only [oracleValue, coinError, Bool.false_eq_true, ite_false, ite_true, smul_add, smul_smul]
  have he : p * (1 / p - 1) + (1 - p) * -1 = 0 := by field_simp; ring
  calc _ = (p + (1 - p)) • g x + (p * (1 / p - 1) + (1 - p) * -1) • h x := by module
    _ = _ := by rw [he]; simp

omit [CompleteSpace E] in
lemma oracle_variance {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (g h : E → E) (x : E) :
    (∫ b, ‖oracleValue p g h x b - g x‖ ^ 2 ∂(coinLaw p hp.le hp1 : Measure Bool)) =
      ((1 - p) / p) * ‖h x‖ ^ 2 := by
  rw [coin_integral]
  simp only [oracleValue, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    coinError, Bool.false_eq_true, ite_false, ite_true, smul_eq_mul]
  field_simp
  ring

omit [CompleteSpace E] in
lemma oracle_increment {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (g h : E → E) (x y : E) :
    (∫ b, ‖(oracleValue p g h x b - oracleValue p g h y b) - (g x - g y)‖ ^ 2
      ∂(coinLaw p hp.le hp1 : Measure Bool)) = ((1 - p) / p) * ‖h x - h y‖ ^ 2 := by
  have he (b : Bool) : (oracleValue p g h x b - oracleValue p g h y b) - (g x - g y) =
      coinError p b • (h x - h y) := by unfold oracleValue; module
  simp only [he]
  rw [coin_integral]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, coinError,
    Bool.false_eq_true, ite_false, ite_true, smul_eq_mul]
  field_simp
  ring

lemma interpolate_norm {r A B ν : ℝ} (hr : 0 ≤ r) (hA : r ≤ A) (hB : r ≤ B)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1) : r ^ 2 ≤ A ^ (2 - 2 * ν) * B ^ (2 * ν) := by
  have hAnn := hr.trans hA
  have hBnn := hr.trans hB
  rcases hr.eq_or_lt with he | hr
  · have hp := mul_nonneg (Real.rpow_nonneg hAnn (2 - 2 * ν)) (Real.rpow_nonneg hBnn (2 * ν))
    simpa only [← he, zero_pow (by decide : 2 ≠ 0)] using hp
  have he : r ^ 2 = r ^ (2 - 2 * ν) * r ^ (2 * ν) := by
    rw [← Real.rpow_add hr, show 2 - 2 * ν + 2 * ν = (2 : ℝ) by ring, Real.rpow_two]
  rw [he]
  exact mul_le_mul
    (Real.rpow_le_rpow hr.le hA (by linarith))
    (Real.rpow_le_rpow hr.le hB (by positivity)) (by positivity) (by positivity)

omit [CompleteSpace E] in
lemma oracle_variance_le {p G : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (g h : E → E) (x : E)
    (hG : ‖h x‖ ≤ G) :
    (∫ b, ‖oracleValue p g h x b - g x‖ ^ 2 ∂(coinLaw p hp.le hp1 : Measure Bool)) ≤ G ^ 2 / p := by
  rw [oracle_variance hp hp1]
  have hc : (1 - p) / p ≤ 1 / p := div_le_div_of_nonneg_right (by linarith) hp.le
  have hp0 : 0 ≤ 1 / p := by positivity
  have hsq : ‖h x‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
  calc _ ≤ (1 / p) * ‖h x‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ (1 / p) * G ^ 2 := mul_le_mul_of_nonneg_left hsq hp0
    _ = _ := by ring

omit [CompleteSpace E] in
lemma oracle_holder {p G H ν : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hH : 0 ≤ H) (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (g h : E → E)
    (hbound : ∀ x, ‖h x‖ ≤ G) (hlip : ∀ x y, ‖h x - h y‖ ≤ H * ‖x - y‖) (x y : E) :
    (∫ b, ‖(oracleValue p g h x b - oracleValue p g h y b) - (g x - g y)‖ ^ 2
      ∂(coinLaw p hp.le hp1 : Measure Bool)) ≤
      ((2 * G) ^ (2 - 2 * ν) * H ^ (2 * ν) / p) * ‖x - y‖ ^ (2 * ν) := by
  have hb : ‖h x - h y‖ ≤ 2 * G := (norm_sub_le _ _).trans (by linarith [hbound x, hbound y])
  have hi := interpolate_norm (norm_nonneg (h x - h y)) hb (hlip x y) hν hν1
  have hc : (1 - p) / p ≤ 1 / p := div_le_div_of_nonneg_right (by linarith) hp.le
  rw [oracle_increment hp hp1]
  calc _ ≤ (1 / p) * ‖h x - h y‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ (1 / p) * ((2 * G) ^ (2 - 2 * ν) * (H * ‖x - y‖) ^ (2 * ν)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [Real.mul_rpow hH (norm_nonneg _)]; ring

end LongTails.Proofs.HolderNoiseHardOracle
