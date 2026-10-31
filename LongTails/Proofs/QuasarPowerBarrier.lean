import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace OracleTemplate.GradientOnlyQuasar

lemma log_one_sub_lower {x : ℝ} (hx : x ≤ 1 / 4) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hp
  have heq : 1 - (1 - x)⁻¹ = -x - x ^ 2 / (1 - x) := by
    field_simp
    ring
  rw [heq] at h
  have hdiv : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ hp).2
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 / 4 - x by linarith)]
  linarith

lemma power_jump_bound {p : ℕ} {u b r s : ℝ}
    (hp : 1 ≤ p) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 ≤ r)
    (hru : 64 * (p : ℝ) ^ 2 * r ≤ u) (hb : b ^ 2 ≤ 4 * r)
    (hs : 0 ≤ s) (hsu : s ≤ 1 - u - b + r) :
    s ^ p ≤ 1 - (p : ℝ) * b := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hpb := mul_le_mul_of_nonneg_left hb (sq_nonneg (p : ℝ))
  have hxsq : ((p : ℝ) * b) ^ 2 ≤ u / 16 := by nlinarith
  have hxb : (p : ℝ) * b ≤ 1 / 4 := by nlinarith [sq_nonneg ((p : ℝ) * b - 1 / 4)]
  have hright : 0 < 1 - (p : ℝ) * b := by linarith
  have hpr : 64 * (p : ℝ) * r ≤ u := by
    have hm := mul_nonneg (show 0 ≤ (p : ℝ) - 1 by linarith)
      (mul_nonneg hp0 hr)
    nlinarith
  have hpu : u ≤ (p : ℝ) * u := by nlinarith
  rcases eq_or_lt_of_le hs with heq | hpos
  · rw [← heq, zero_pow (by omega : p ≠ 0)]
    exact hright.le
  · apply (Real.log_le_log_iff (pow_pos hpos p) hright).mp
    rw [Real.log_pow]
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) hp0
    have hscale := mul_le_mul_of_nonneg_left hsu hp0
    have hlower := log_one_sub_lower hxb
    nlinarith

def barrier (q : ℝ) : ℝ := 1 - (max 0 (1 - q)) ^ 2

def barrierSlope (q : ℝ) : ℝ := 2 * max 0 (1 - q)

lemma barrier_le_one (q : ℝ) : barrier q ≤ 1 := by
  unfold barrier
  nlinarith [sq_nonneg (max 0 (1 - q))]

lemma barrier_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ barrier q := by
  unfold barrier
  by_cases h : q ≤ 1
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    norm_num

lemma barrier_le_twice (q : ℝ) : barrier q ≤ 2 * q := by
  unfold barrier
  by_cases h : q ≤ 1
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg q]
  · rw [max_eq_left (by linarith)]
    nlinarith

lemma barrier_eq_one {q : ℝ} (hq : 1 ≤ q) : barrier q = 1 := by
  simp [barrier, max_eq_left (by linarith : 1 - q ≤ 0)]

lemma barrierSlope_nonneg (q : ℝ) : 0 ≤ barrierSlope q := by
  unfold barrierSlope
  positivity

lemma barrier_tangent (q r : ℝ) :
    barrier r ≤ barrier q + barrierSlope q * (r - q) := by
  unfold barrier barrierSlope
  by_cases hq : q ≤ 1 <;> by_cases hr : r ≤ 1
  · rw [max_eq_right (by linarith : 0 ≤ 1 - q),
      max_eq_right (by linarith : 0 ≤ 1 - r)]
    nlinarith [sq_nonneg (r - q)]
  · rw [max_eq_right (by linarith : 0 ≤ 1 - q),
      max_eq_left (by linarith : 1 - r ≤ 0)]
    nlinarith [mul_nonneg (show 0 ≤ 1 - q by linarith) (show 0 ≤ r - 1 by linarith),
      sq_nonneg (1 - q)]
  · rw [max_eq_left (by linarith : 1 - q ≤ 0),
      max_eq_right (by linarith : 0 ≤ 1 - r)]
    nlinarith [sq_nonneg (1 - r)]
  · rw [max_eq_left (by linarith : 1 - q ≤ 0),
      max_eq_left (by linarith : 1 - r ≤ 0)]
    norm_num

lemma continuous_barrier : Continuous barrier := by
  unfold barrier
  fun_prop

lemma continuous_barrierSlope : Continuous barrierSlope := by
  unfold barrierSlope
  fun_prop

lemma hasDerivAt_barrier (q : ℝ) : HasDerivAt barrier (barrierSlope q) q := by
  have hpoly (x : ℝ) : HasDerivAt (fun t : ℝ => 1 - (1 - t) ^ 2) (2 * (1 - x)) x := by
    have hb : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      convert! (hasDerivAt_id x).const_sub (1 : ℝ) using 1
    convert! (hasDerivAt_const x 1).sub (hb.pow 2) using 1
    ring
  rcases lt_trichotomy q 1 with hq | rfl | hq
  · have h := hpoly q
    rw [show barrierSlope q = 2 * (1 - q) by
      simp [barrierSlope, max_eq_right (by linarith : 0 ≤ 1 - q)]]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hq] with t ht
    simp [barrier, max_eq_right (by linarith : 0 ≤ 1 - t)]
  · have hl : HasDerivWithinAt barrier 0 (Set.Iic 1) 1 := by
      have h : HasDerivWithinAt (fun t : ℝ => 1 - (1 - t) ^ 2) 0 (Set.Iic 1) 1 := by
        simpa using (hpoly 1).hasDerivWithinAt (s := Set.Iic 1)
      apply h.congr
      · intro t ht
        change t ≤ 1 at ht
        simp [barrier, max_eq_right (sub_nonneg.mpr ht)]
      · norm_num [barrier]
    have hr : HasDerivWithinAt barrier 0 (Set.Ici 1) 1 := by
      apply (hasDerivWithinAt_const (1 : ℝ) (Set.Ici 1) (1 : ℝ)).congr
      · intro t ht
        exact barrier_eq_one ht
      · norm_num [barrier]
    simpa [barrierSlope] using hl.union hr
  · rw [show barrierSlope q = 0 by
      simp [barrierSlope, max_eq_left (by linarith : 1 - q ≤ 0)]]
    apply (hasDerivAt_const q (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hq] with t ht
    exact barrier_eq_one ht.le

lemma barrier_ge_self {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) : q ≤ barrier q := by
  rw [barrier, max_eq_right (sub_nonneg.mpr hq1)]
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1)]

lemma rescaled_power_drift {p : ℕ} {P E J d b : ℝ}
    (hp : 1 ≤ p) (hP : 0 < P) (hE : 0 < E)
    (hd : d ≤ P * b) (hJ : (J / P) ^ p ≤ 1 - (p : ℝ) * b) :
    (p : ℝ) * (P / E) ^ (p - 1) * (d / E) + (J / E) ^ p - (P / E) ^ p ≤ 0 := by
  have hq : 0 ≤ (P / E) ^ p := by positivity
  have hratio : (J / E) ^ p = (J / P) ^ p * (P / E) ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hh := mul_le_mul_of_nonneg_right hJ hq
  rw [← hratio] at hh
  have hflow : (p : ℝ) * (P / E) ^ (p - 1) * (d / E) ≤
      (p : ℝ) * (P / E) ^ p * b := by
    have hd' := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ (p : ℝ) * (P / E) ^ (p - 1) / E by positivity)
    have heq : (P / E) ^ (p - 1) * (P / E) = (P / E) ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel hp]
    calc
      _ = ((p : ℝ) * (P / E) ^ (p - 1) / E) * d := by ring
      _ ≤ ((p : ℝ) * (P / E) ^ (p - 1) / E) * (P * b) := hd'
      _ = (p : ℝ) * ((P / E) ^ (p - 1) * (P / E)) * b := by ring
      _ = _ := by rw [heq]
  nlinarith

lemma barrier_generator {q j d : ℝ} (h : d + j - q ≤ 0) :
    barrierSlope q * d + barrier j - barrier q ≤ 0 := by
  have ht := barrier_tangent q j
  have hh := mul_nonneg (barrierSlope_nonneg q) (show 0 ≤ -(d + j - q) by linarith)
  nlinarith

lemma barrier_jump_le_four {q j : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hj : j ≤ 5 / 4 * q) : barrier j ≤ 4 * barrier q := by
  have hlow := barrier_ge_self hq hq1
  have hup := barrier_le_twice j
  nlinarith

end OracleTemplate.GradientOnlyQuasar
