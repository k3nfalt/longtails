import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.FiniteMomentMirrorGeometry

lemma concave_power_tangent {a b r : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    b ^ r ≤ a ^ r + r * a ^ (r - 1) * (b - a) := by
  have ht := rpow_one_add_le_one_add_mul_self
    (s := b / a - 1) (by have := div_nonneg hb ha.le; linarith) hr hr1
  have he : 1 + (b / a - 1) = b / a := by ring
  rw [he, Real.div_rpow hb ha.le] at ht
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos ha r)).mp ht
  have hp : a ^ (r - 1) = a ^ r / a := by
    rw [Real.rpow_sub ha, Real.rpow_one]
  rw [hp]
  convert hh using 1; field_simp

lemma truncated_square_le_power {t p : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    (min t 2) ^ 2 ≤ 4 * t ^ p := by
  by_cases h : t ≤ 1
  · have hm : min t 2 = t := min_eq_left (by linarith)
    rw [hm]
    have hs : t ^ (2 : ℝ) ≤ t ^ p := Real.rpow_le_rpow_of_exponent_ge' ht h hp hp2
    rw [Real.rpow_two] at hs
    have hn := Real.rpow_nonneg ht p
    linarith
  · have ht1 : 1 ≤ t := le_of_lt (lt_of_not_ge h)
    have hs : 1 ≤ t ^ p := Real.one_le_rpow ht1 hp
    have hm : 0 ≤ min t 2 := le_min ht (by norm_num)
    have hm2 : min t 2 ≤ 2 := min_le_right _ _
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def primalOfDual (p : ℝ) (v : E) : E := ‖v‖ ^ (p - 2) • v

lemma norm_power_tangent {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (v h : E) (hv : v ≠ 0) :
    ‖v + h‖ ^ p ≤ ‖v‖ ^ p + p * ‖v‖ ^ (p - 2) * inner ℝ v h +
      (p / 2) * ‖v‖ ^ (p - 2) * ‖h‖ ^ 2 := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht := concave_power_tangent (sq_pos_of_pos hpos) (sq_nonneg ‖v + h‖)
    (show 0 ≤ p / 2 by linarith) (show p / 2 ≤ 1 by linarith)
  have he (w : E) : (‖w‖ ^ 2) ^ (p / 2) = ‖w‖ ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have he' : (‖v‖ ^ 2) ^ (p / 2 - 1) = ‖v‖ ^ (p - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  rw [he, he, he', norm_add_sq_real] at ht
  nlinarith

lemma norm_power_remainder_small {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (v h : E) (hv : v ≠ 0) (hhv : ‖h‖ ≤ ‖v‖) :
    ‖v + h‖ ^ p ≤ ‖v‖ ^ p + p * ‖v‖ ^ (p - 2) * inner ℝ v h +
      (p / 2) * ‖h‖ ^ p := by
  by_cases hh : h = 0
  · subst h
    simp [Real.zero_rpow hp.ne']
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hr := Real.rpow_le_rpow_of_nonpos hhpos hhv (show p - 2 ≤ 0 by linarith)
  have hm := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖h‖)
  have he : ‖h‖ ^ (p - 2) * ‖h‖ ^ 2 = ‖h‖ ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_add hhpos]
    congr 1
    ring
  rw [he] at hm
  have ht := norm_power_tangent hp.le hp2 v h hv
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ p / 2 by linarith)
  nlinarith

lemma norm_power_remainder_large {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (v h : E) (hvh : ‖v‖ ≤ ‖h‖) :
    ‖v + h‖ ^ p ≤ ‖v‖ ^ p + p * ‖v‖ ^ (p - 2) * inner ℝ v h +
      6 * ‖h‖ ^ p := by
  have hn : ‖v + h‖ ≤ 2 * ‖h‖ := (norm_add_le v h).trans (by linarith)
  have ht := Real.rpow_le_rpow (norm_nonneg _) hn (show 0 ≤ p by linarith)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)] at ht
  have htwo : (2 : ℝ) ^ p ≤ 4 := by
    simpa only [Real.rpow_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp2
  have ht' := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (norm_nonneg h) p)
  have he (w : E) : ‖w‖ ^ (p - 2) * ‖w‖ = ‖w‖ ^ (p - 1) := by
    have ht := Real.rpow_add' (norm_nonneg w) (by linarith : p - 2 + 1 ≠ 0)
    rw [Real.rpow_one] at ht
    convert ht.symm using 1; congr 1; ring
  have he' : ‖h‖ ^ (p - 1) * ‖h‖ = ‖h‖ ^ p := by
    have ht := Real.rpow_add' (norm_nonneg h) (by linarith : p - 1 + 1 ≠ 0)
    rw [Real.rpow_one] at ht
    convert ht.symm using 1; congr 1; ring
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm v h)
  have hi' := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (norm_nonneg v) (p - 2))
  have hr := Real.rpow_le_rpow (norm_nonneg v) hvh (show 0 ≤ p - 1 by linarith)
  have hr' := mul_le_mul_of_nonneg_right hr (norm_nonneg h)
  rw [he'] at hr'
  have hb : -‖h‖ ^ p ≤ ‖v‖ ^ (p - 2) * inner ℝ v h := by
    have hei : ‖v‖ ^ (p - 2) * (‖v‖ * ‖h‖) = ‖v‖ ^ (p - 1) * ‖h‖ := by
      rw [← mul_assoc, he]
    nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ p by linarith)
  have hpow := Real.rpow_nonneg (norm_nonneg h) p
  have hvpow := Real.rpow_nonneg (norm_nonneg v) p
  nlinarith

lemma norm_power_smooth {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (v h : E) :
    ‖v + h‖ ^ p ≤ ‖v‖ ^ p + p * ‖v‖ ^ (p - 2) * inner ℝ v h +
      6 * ‖h‖ ^ p := by
  by_cases hv : v = 0
  · subst v
    simp only [zero_add, norm_zero, inner_zero_left, mul_zero, add_zero,
      Real.zero_rpow (show p ≠ 0 by linarith), zero_add]
    have := Real.rpow_nonneg (norm_nonneg h) p
    linarith
  by_cases hh : ‖h‖ ≤ ‖v‖
  · have ht := norm_power_remainder_small (show 0 < p by linarith) hp2 v h hv hh
    have hn := Real.rpow_nonneg (norm_nonneg h) p
    nlinarith
  · exact norm_power_remainder_large hp hp2 v h (le_of_lt (lt_of_not_ge hh))

lemma norm_primalOfDual {p : ℝ} (hp : 1 < p) (v : E) :
    ‖primalOfDual p v‖ = ‖v‖ ^ (p - 1) := by
  rw [primalOfDual, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg v) _)]
  have ht := Real.rpow_add' (norm_nonneg v) (by linarith : p - 2 + 1 ≠ 0)
  rw [Real.rpow_one] at ht
  convert ht.symm using 1; congr 1; ring


end LongTails.Proofs.FiniteMomentMirrorGeometry
