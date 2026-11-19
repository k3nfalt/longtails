import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace LongTails.Proofs.BlumGladyshevValley

noncomputable def valley (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2) - 1

noncomputable def slope (t : ℝ) : ℝ := t / Real.sqrt (1 + t ^ 2)

lemma valley_nonneg (t : ℝ) : 0 ≤ valley t := by
  unfold valley
  have h := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  nlinarith [Real.sqrt_nonneg (1 + t ^ 2), sq_nonneg t]

@[simp] lemma valley_zero : valley 0 = 0 := by norm_num [valley]

@[simp] lemma slope_zero : slope 0 = 0 := by norm_num [slope]

lemma valley_derivative (t : ℝ) : HasDerivAt valley (slope t) t := by
  have h : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_add 1 using 1 <;> simp
  have hp : 0 < 1 + t ^ 2 := by positivity
  change HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2) - 1) _ t
  convert (h.sqrt hp.ne').sub_const 1 using 1
  unfold slope
  field_simp

lemma slope_abs_le_one (t : ℝ) : |slope t| ≤ 1 := by
  have hp : 0 < 1 + t ^ 2 := by positivity
  rw [slope, abs_div, abs_of_pos (Real.sqrt_pos.2 hp), div_le_one (Real.sqrt_pos.2 hp)]
  nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (1 + t ^ 2), sq_abs t, abs_nonneg t]

lemma slope_abs_le_abs (t : ℝ) : |slope t| ≤ |t| := by
  have hp : 0 < 1 + t ^ 2 := by positivity
  have h := valley_nonneg t
  unfold valley at h
  rw [slope, abs_div, abs_of_pos (Real.sqrt_pos.2 hp), div_le_iff₀ (Real.sqrt_pos.2 hp)]
  nlinarith [mul_nonneg (abs_nonneg t) h]

lemma valley_support (x y : ℝ) : valley x + slope x * (y - x) ≤ valley y := by
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hx' := Real.sqrt_pos.2 hx
  have hy' := Real.sqrt_pos.2 hy
  have hprod : 1 + x * y ≤ Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by
    have hsq : (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) ^ 2 =
        (1 + x ^ 2) * (1 + y ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
    nlinarith [sq_nonneg (x-y), mul_pos hx' hy']
  unfold valley slope
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

lemma valley_small {t : ℝ} (h : valley t ≤ 1 / 512) : |t| ≤ 1 / 8 := by
  unfold valley at h
  have h1 : Real.sqrt (1 + t ^ 2) ≤ 513 / 512 := by linarith
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (by positivity)] at h2
  rw [abs_le]
  constructor <;> nlinarith

lemma separated (t s : ℝ) :
    1 < 512 * (valley (t - 1 / 2) + valley (t + s)) ∨
    1 < 512 * (valley (t - 1 / 2) + valley (t - s)) := by
  by_contra! h
  have h0 := valley_small (t := t - 1 / 2) (by linarith [valley_nonneg (t+s), h.1])
  have hp := valley_small (t := t+s) (by linarith [valley_nonneg (t-1/2), h.1])
  have hm := valley_small (t := t-s) (by linarith [valley_nonneg (t-1/2), h.2])
  rw [abs_le] at h0 hp hm
  linarith [h0.1, hp.2, hm.2]

end LongTails.Proofs.BlumGladyshevValley
