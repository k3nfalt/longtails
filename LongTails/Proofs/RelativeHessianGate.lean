import LongTails.Proofs.QuasarHardProfiles
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace LongTails.Proofs.RelativeHessianGate

open Filter Set
open scoped Topology

noncomputable def positivePower (k : ℕ) (x : ℝ) : ℝ := max x 0 ^ k

lemma positivePower_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (positivePower (k + 2)) ((k + 2 : ℕ) * max x 0 ^ (k + 1)) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] positivePower (k + 2) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [positivePower, max_eq_right hy.le]
    simpa [max_eq_right hx.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he.symm
  · subst x
    simp only [max_self, zero_pow (by omega : k + 1 ≠ 0), mul_zero]
    apply HasDerivAt.of_isLittleO
    have hb : (fun y : ℝ => positivePower (k + 2) y - positivePower (k + 2) 0 -
        (y - 0) • (0 : ℝ)) =O[𝓝 0] (fun y : ℝ => ‖y - 0‖ ^ (k + 2)) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [] with y
      simp only [positivePower, max_self, zero_pow (by omega : k + 2 ≠ 0),
        sub_zero, smul_zero, one_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (le_max_right y 0) _),
        abs_of_nonneg (pow_nonneg (abs_nonneg y) _)]
      exact pow_le_pow_left₀ (le_max_right y 0) (max_le (le_abs_self y) (abs_nonneg y)) _
    exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub (0 : ℝ) (by omega : 1 < k + 2))
  · have he : (fun y : ℝ => y ^ (k + 2)) =ᶠ[𝓝 x] positivePower (k + 2) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp [positivePower, max_eq_left hy.le]
    simpa [max_eq_left hx.le, Nat.add_sub_cancel] using
      ((hasDerivAt_id x).pow (k + 2)).congr_of_eventuallyEq he.symm

lemma positivePower_contDiff (k : ℕ) : ContDiff ℝ k (positivePower (k + 1)) := by
  induction k with
  | zero =>
      exact contDiff_zero.mpr (by unfold positivePower; fun_prop)
  | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one]
      apply contDiff_succ_iff_deriv.mpr
      refine ⟨fun x => (positivePower_hasDerivAt k x).differentiableAt, by simp, ?_⟩
      have hd : deriv (positivePower (k + 2)) = fun x => (k + 2 : ℕ) * positivePower (k + 1) x := by
        funext x
        exact (positivePower_hasDerivAt k x).deriv
      rw [hd]
      exact contDiff_const.mul ih

lemma positivePower_affine_hasDerivAt (k : ℕ) (a b x : ℝ) :
    HasDerivAt (fun t => positivePower (k + 2) (a * t + b))
      (((k + 2 : ℕ) : ℝ) * positivePower (k + 1) (a * x + b) * a) x := by
  simpa [positivePower, Function.comp_def] using
    (positivePower_hasDerivAt k (a * x + b)).comp x
      ((hasDerivAt_id x).const_mul a |>.add_const b)

noncomputable def spline (k : ℕ) (t : ℝ) : ℝ :=
  positivePower k t - 4 * positivePower k (t - 1) + 6 * positivePower k (t - 2) -
    4 * positivePower k (t - 3) + positivePower k (t - 4)

noncomputable def gate (t : ℝ) : ℝ := spline 4 (40 * t - 4) / 24
noncomputable def gateSlope (t : ℝ) : ℝ := (20 / 3 : ℝ) * spline 3 (40 * t - 4)
noncomputable def gateCurvature (t : ℝ) : ℝ := 800 * spline 2 (40 * t - 4)
noncomputable def gateThird (t : ℝ) : ℝ := 64000 * spline 1 (40 * t - 4)

lemma spline_contDiff (k : ℕ) : ContDiff ℝ k (spline (k + 1)) := by
  have hp := positivePower_contDiff k
  unfold spline
  fun_prop

lemma spline_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (spline (k + 2)) (((k + 2 : ℕ) : ℝ) * spline (k + 1) t) t := by
  have h := (((((positivePower_hasDerivAt k t).sub
    ((positivePower_hasDerivAt k (t - 1)).comp t ((hasDerivAt_id t).sub_const 1) |>.const_mul 4)).add
    ((positivePower_hasDerivAt k (t - 2)).comp t ((hasDerivAt_id t).sub_const 2) |>.const_mul 6)).sub
    ((positivePower_hasDerivAt k (t - 3)).comp t ((hasDerivAt_id t).sub_const 3) |>.const_mul 4)).add
    ((positivePower_hasDerivAt k (t - 4)).comp t ((hasDerivAt_id t).sub_const 4)))
  convert h using 1
  · funext x; rfl
  · simp only [spline, positivePower, mul_one]
    ring

lemma gate_contDiff : ContDiff ℝ 3 gate := by
  have hs := spline_contDiff 3
  unfold gate
  fun_prop

lemma gate_hasDerivAt (t : ℝ) : HasDerivAt gate (gateSlope t) t := by
  have h := ((spline_hasDerivAt 2 (40 * t - 4)).comp t
    ((hasDerivAt_id t).const_mul 40 |>.sub_const 4)).div_const 24
  convert h using 1
  · funext x; rfl
  · norm_num [gateSlope]
    ring

lemma gateSlope_hasDerivAt (t : ℝ) : HasDerivAt gateSlope (gateCurvature t) t := by
  have h := ((spline_hasDerivAt 1 (40 * t - 4)).comp t
    ((hasDerivAt_id t).const_mul 40 |>.sub_const 4)).const_mul (20 / 3)
  convert h using 1
  · funext x; rfl
  · norm_num [gateCurvature]
    ring

lemma gateCurvature_hasDerivAt (t : ℝ) : HasDerivAt gateCurvature (gateThird t) t := by
  have h := ((spline_hasDerivAt 0 (40 * t - 4)).comp t
    ((hasDerivAt_id t).const_mul 40 |>.sub_const 4)).const_mul 800
  convert h using 1
  · funext x; rfl
  · norm_num [gateThird]
    ring

lemma spline_zero {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : t ≤ 0) : spline k t = 0 := by
  simp [spline, positivePower, max_eq_right ht, max_eq_right (by linarith : t - 1 ≤ 0),
    max_eq_right (by linarith : t - 2 ≤ 0), max_eq_right (by linarith : t - 3 ≤ 0),
    max_eq_right (by linarith : t - 4 ≤ 0), zero_pow hk]

lemma spline_tail {t : ℝ} (ht : 4 ≤ t) :
    spline 4 t = 24 ∧ spline 3 t = 0 ∧ spline 2 t = 0 ∧ spline 1 t = 0 := by
  simp only [spline, positivePower, max_eq_left (show 0 ≤ t by linarith),
    max_eq_left (show 0 ≤ t - 1 by linarith), max_eq_left (show 0 ≤ t - 2 by linarith),
    max_eq_left (show 0 ≤ t - 3 by linarith), max_eq_left (show 0 ≤ t - 4 by linarith)]
  constructor; ring
  constructor; ring
  constructor <;> ring

lemma gate_flat {t : ℝ} (ht : t ≤ 1 / 10) :
    gate t = 0 ∧ gateSlope t = 0 ∧ gateCurvature t = 0 ∧ gateThird t = 0 := by
  have h : 40 * t - 4 ≤ 0 := by linarith
  simp [gate, gateSlope, gateCurvature, gateThird, spline_zero (by norm_num : 4 ≠ 0) h,
    spline_zero (by norm_num : 3 ≠ 0) h, spline_zero (by norm_num : 2 ≠ 0) h,
    spline_zero (by norm_num : 1 ≠ 0) h]

lemma gate_saturated {t : ℝ} (ht : 1 / 5 ≤ t) :
    gate t = 1 ∧ gateSlope t = 0 ∧ gateCurvature t = 0 ∧ gateThird t = 0 := by
  have h := spline_tail (show 4 ≤ 40 * t - 4 by linarith)
  simp [gate, gateSlope, gateCurvature, gateThird, h.1, h.2.1, h.2.2.1, h.2.2.2]

lemma spline_three_nonneg (t : ℝ) : 0 ≤ spline 3 t := by
  by_cases h0 : t ≤ 0
  · rw [spline_zero (by norm_num : 3 ≠ 0) h0]
  have ht : 0 ≤ t := le_of_not_ge h0
  by_cases h1 : t ≤ 1
  · simp [spline, positivePower, max_eq_left ht, max_eq_right (by linarith : t - 1 ≤ 0),
      max_eq_right (by linarith : t - 2 ≤ 0), max_eq_right (by linarith : t - 3 ≤ 0),
      max_eq_right (by linarith : t - 4 ≤ 0), pow_nonneg ht]
  have ht1 : 0 ≤ t - 1 := by linarith
  by_cases h2 : t ≤ 2
  · simp only [spline, positivePower, max_eq_left ht, max_eq_left ht1,
      max_eq_right (show t - 2 ≤ 0 by linarith), max_eq_right (show t - 3 ≤ 0 by linarith),
      max_eq_right (show t - 4 ≤ 0 by linarith), zero_pow (by norm_num : 3 ≠ 0), mul_zero, add_zero, sub_zero]
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (show 0 ≤ 2 - t by linarith), sq_nonneg (t - 1)]
  have ht2 : 0 ≤ t - 2 := by linarith
  by_cases h3 : t ≤ 3
  · simp only [spline, positivePower, max_eq_left ht, max_eq_left ht1, max_eq_left ht2,
      max_eq_right (show t - 3 ≤ 0 by linarith), max_eq_right (show t - 4 ≤ 0 by linarith),
      zero_pow (by norm_num : 3 ≠ 0), mul_zero, add_zero, sub_zero]
    nlinarith [mul_nonneg (sq_nonneg (3 - t)) ht2, sq_nonneg (3 - t)]
  have ht3 : 0 ≤ t - 3 := by linarith
  by_cases h4 : t ≤ 4
  · simp only [spline, positivePower, max_eq_left ht, max_eq_left ht1, max_eq_left ht2,
      max_eq_left ht3, max_eq_right (show t - 4 ≤ 0 by linarith),
      zero_pow (by norm_num : 3 ≠ 0), add_zero]
    nlinarith [pow_nonneg (show 0 ≤ 4 - t by linarith) 3]
  · rw [(spline_tail (le_of_not_ge h4)).2.1]

lemma gateSlope_nonneg (t : ℝ) : 0 ≤ gateSlope t := by
  unfold gateSlope
  exact mul_nonneg (by norm_num) (spline_three_nonneg _)

lemma gate_monotone : Monotone gate := monotone_of_hasDerivAt_nonneg gate_hasDerivAt gateSlope_nonneg

lemma gate_bounds (t : ℝ) : 0 ≤ gate t ∧ gate t ≤ 1 := by
  constructor
  · by_cases ht : t ≤ 1 / 10
    · rw [(gate_flat ht).1]
    · have h := gate_monotone (le_of_not_ge ht)
      rwa [(gate_flat (le_refl (1 / 10 : ℝ))).1] at h
  · by_cases ht : 1 / 5 ≤ t
    · rw [(gate_saturated ht).1]
    · have h := gate_monotone (le_of_not_ge ht)
      rwa [(gate_saturated (le_refl (1 / 5 : ℝ))).1] at h

lemma spline_bound {t : ℝ} (_ht0 : 0 ≤ t) (ht4 : t ≤ 4) (k : ℕ) : |spline k t| ≤ 16 * 4 ^ k := by
  have h (j : ℝ) (hj : 0 ≤ j) : 0 ≤ positivePower k (t - j) ∧ positivePower k (t - j) ≤ 4 ^ k := by
    unfold positivePower
    refine ⟨by positivity, ?_⟩
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (by norm_num)) k
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  simp only [sub_zero] at h0
  unfold spline
  rw [abs_le]
  constructor <;> linarith

lemma gate_jet_bounds (t : ℝ) : |gateSlope t| ≤ 2 ^ 24 ∧ |gateCurvature t| ≤ 2 ^ 24 ∧
    |gateThird t| ≤ 2 ^ 24 := by
  by_cases ht0 : t ≤ 1 / 10
  · obtain ⟨_, h1, h2, h3⟩ := gate_flat ht0
    rw [h1, h2, h3]
    norm_num
  by_cases ht1 : 1 / 5 ≤ t
  · obtain ⟨_, h1, h2, h3⟩ := gate_saturated ht1
    rw [h1, h2, h3]
    norm_num
  have hz0 : 0 ≤ 40 * t - 4 := by linarith
  have hz4 : 40 * t - 4 ≤ 4 := by linarith
  have h1 := spline_bound hz0 hz4 3
  have h2 := spline_bound hz0 hz4 2
  have h3 := spline_bound hz0 hz4 1
  norm_num [gateSlope, gateCurvature, gateThird, abs_mul, abs_div] at *
  constructor; linarith
  constructor <;> linarith

end LongTails.Proofs.RelativeHessianGate
