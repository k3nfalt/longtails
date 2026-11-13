import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv

open Set Filter
open scoped Topology ContDiff

namespace LongTails.Proofs.CompactSmoothMaximum

lemma hasDerivAt_join (f g df dg : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hc : f c = g c) (hd : df c = dg c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then df x else dg x) x := by
  rcases lt_trichotomy x c with hx | rfl | hx
  · simp only [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    simp only [ite_eq_left hy.le]
  · simp only [le_refl, ↓reduceIte]
    have hl : HasDerivWithinAt (fun y => if y ≤ x then f y else g y)
        (df x) (Iic x) x := by
      apply (hf x).hasDerivWithinAt.congr
      · intro y hy
        simp only [ite_eq_left (show y ≤ x from hy)]
      · simp
    have hr : HasDerivWithinAt (fun y => if y ≤ x then f y else g y)
        (df x) (Ioi x) x := by
      rw [hd]
      apply (hg x).hasDerivWithinAt.congr
      · intro y hy
        simp only [ite_eq_right (not_le.mpr (show x < y from hy))]
      · simpa using hc
    have hh := hl.union hr
    simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hh
  · simp only [ite_eq_right (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    simp only [ite_eq_right (not_le.mpr hy)]

noncomputable def ramp (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 then x ^ 3 - x ^ 4 / 2 else x - 1 / 2

noncomputable def slope (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 then 3 * x ^ 2 - 2 * x ^ 3 else 1

noncomputable def curvature (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 then 6 * x - 6 * x ^ 2 else 0

lemma middle_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 - y ^ 4 / 2) (3 * x ^ 2 - 2 * x ^ 3) x := by
  convert ((hasDerivAt_id x).pow 3).sub (((hasDerivAt_id x).pow 4).div_const 2) using 1
  · rfl
  · dsimp
    ring

lemma middle_second_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 2 * y ^ 3) (6 * x - 6 * x ^ 2) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul 3).sub
    (((hasDerivAt_id x).pow 3).const_mul 2) using 1
  · funext y
    dsimp
  · dsimp
    ring

lemma ramp_hasDerivAt (x : ℝ) : HasDerivAt ramp (slope x) x := by
  have hi := hasDerivAt_join (fun y => y ^ 3 - y ^ 4 / 2) (fun y => y - 1 / 2)
    (fun y => 3 * y ^ 2 - 2 * y ^ 3) (fun _ => 1) 1 middle_derivative
    (fun y => (hasDerivAt_id y).sub_const (1 / 2)) (by norm_num) (by norm_num)
  exact hasDerivAt_join (fun _ => 0) _ (fun _ => 0) _ 0
    (fun y => hasDerivAt_const y 0) hi (by norm_num) (by norm_num) x

lemma slope_hasDerivAt (x : ℝ) : HasDerivAt slope (curvature x) x := by
  have hi := hasDerivAt_join (fun y => 3 * y ^ 2 - 2 * y ^ 3) (fun _ => 1)
    (fun y => 6 * y - 6 * y ^ 2) (fun _ => 0) 1 middle_second_derivative
    (fun y => hasDerivAt_const y 1) (by norm_num) (by norm_num)
  exact hasDerivAt_join (fun _ => 0) _ (fun _ => 0) _ 0
    (fun y => hasDerivAt_const y 0) hi (by norm_num) (by norm_num) x

lemma curvature_bounds (x : ℝ) : 0 ≤ curvature x ∧ curvature x ≤ 3 / 2 := by
  by_cases h : x ≤ 0
  · simp [curvature, h]
    norm_num
  · by_cases h' : x ≤ 1
    · simp only [curvature, ite_eq_right h, ite_eq_left h']
      constructor <;> nlinarith [sq_nonneg (x - 1 / 2),
        mul_nonneg (le_of_not_ge h) (sub_nonneg.mpr h')]
    · norm_num [curvature, h, h']

lemma curvature_eq (x : ℝ) : curvature x = 6 * max 0 x * max 0 (1 - x) := by
  by_cases h : x ≤ 0
  · simp [curvature, h]
  · by_cases h' : x ≤ 1
    · simp only [curvature, ite_eq_right h, ite_eq_left h',
        max_eq_right (le_of_not_ge h), max_eq_right (sub_nonneg.mpr h')]
      ring
    · simp [curvature, h, h', max_eq_left (show 1 - x ≤ 0 by linarith)]

lemma curvature_continuous : Continuous curvature := by
  simp_rw [funext curvature_eq]
  fun_prop

lemma slope_bounds (x : ℝ) : 0 ≤ slope x ∧ slope x ≤ 1 := by
  by_cases h : x ≤ 0
  · norm_num [slope, h]
  · by_cases h' : x ≤ 1
    · simp only [slope, ite_eq_right h, ite_eq_left h']
      constructor
      · nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 3 - 2 * x by linarith)]
      · nlinarith [mul_nonneg (sq_nonneg (1 - x)) (show 0 ≤ 1 + 2 * x by linarith)]
    · norm_num [slope, h, h']

lemma deriv_ramp : deriv ramp = slope := funext fun x => (ramp_hasDerivAt x).deriv

lemma deriv_slope : deriv slope = curvature := funext fun x => (slope_hasDerivAt x).deriv

lemma ramp_contDiff : ContDiff ℝ 2 ramp := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (ramp_hasDerivAt x).differentiableAt, ?_, ?_⟩
  · simp
  · rw [deriv_ramp, contDiff_one_iff_deriv, deriv_slope]
    exact ⟨fun x => (slope_hasDerivAt x).differentiableAt, curvature_continuous⟩

lemma ramp_convex : ConvexOn ℝ univ ramp := by
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun x => (ramp_hasDerivAt x).differentiableAt
  · rw [deriv_ramp]
    exact fun x => (slope_hasDerivAt x).differentiableAt
  · intro x
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      deriv_ramp, deriv_slope] using (curvature_bounds x).1

lemma ramp_nonneg (x : ℝ) : 0 ≤ ramp x := by
  by_cases h : x ≤ 0
  · simp [ramp, h]
  · by_cases h' : x ≤ 1
    · simp only [ramp, ite_eq_right h, ite_eq_left h']
      have hx : 0 ≤ x ^ 3 := pow_nonneg (le_of_not_ge h) _
      nlinarith [mul_nonneg hx (show 0 ≤ 1 - x / 2 by linarith)]
    · simp only [ramp, ite_eq_right h, ite_eq_right h']
      linarith

lemma ramp_above_linear (x : ℝ) : x - 1 / 2 ≤ ramp x := by
  by_cases h : x ≤ 0
  · simp only [ramp, ite_eq_left h]
    linarith
  · by_cases h' : x ≤ 1
    · simp only [ramp, ite_eq_right h, ite_eq_left h']
      have hn : 0 ≤ (1 - x) ^ 3 * (1 + x) :=
        mul_nonneg (pow_nonneg (sub_nonneg.mpr h') _) (by linarith)
      nlinarith
    · simp [ramp, h, h']

noncomputable def smoothPositive (T x : ℝ) : ℝ := 2 * T * ramp ((x + T) / (2 * T))

lemma smoothPositive_nonneg {T : ℝ} (hT : 0 < T) (x : ℝ) :
    0 ≤ smoothPositive T x :=
  mul_nonneg (by positivity) (ramp_nonneg _)

lemma smoothPositive_above {T : ℝ} (hT : 0 < T) (x : ℝ) :
    x ≤ smoothPositive T x := by
  have hh := mul_le_mul_of_nonneg_left (ramp_above_linear ((x + T) / (2 * T)))
    (show 0 ≤ 2 * T by positivity)
  have he : 2 * T * ((x + T) / (2 * T) - 1 / 2) = x := by
    field_simp
    ring
  rw [he] at hh
  exact hh

lemma smoothPositive_left {T x : ℝ} (hT : 0 < T) (hx : x ≤ -T) :
    smoothPositive T x = 0 := by
  have hh : (x + T) / (2 * T) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [smoothPositive, ramp, hh]

lemma smoothPositive_right {T x : ℝ} (hT : 0 < T) (hx : T ≤ x) :
    smoothPositive T x = x := by
  have hh : 1 ≤ (x + T) / (2 * T) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have he : ramp ((x + T) / (2 * T)) = (x + T) / (2 * T) - 1 / 2 := by
    rcases eq_or_lt_of_le hh with he | he
    · rw [← he]
      norm_num [ramp]
    · simp [ramp, not_le.mpr (lt_trans (show (0 : ℝ) < 1 by norm_num) he), not_le.mpr he]
  unfold smoothPositive
  rw [he]
  field_simp
  ring

lemma smoothPositive_contDiff (T : ℝ) : ContDiff ℝ 2 (smoothPositive T) := by
  unfold smoothPositive
  exact contDiff_const.mul (ramp_contDiff.comp ((contDiff_id.add contDiff_const).div_const _))

lemma smoothPositive_hasDerivAt {T : ℝ} (hT : 0 < T) (x : ℝ) :
    HasDerivAt (smoothPositive T) (slope ((x + T) / (2 * T))) x := by
  have ha := ((hasDerivAt_id x).add_const T).div_const (2 * T)
  have hh := ((ramp_hasDerivAt _).comp x ha).const_mul (2 * T)
  convert hh using 1
  · ext y
    rfl
  · dsimp
    field_simp

lemma smoothPositive_second_hasDerivAt (T x : ℝ) :
    HasDerivAt (fun y => slope ((y + T) / (2 * T)))
      (curvature ((x + T) / (2 * T)) / (2 * T)) x := by
  have ha := ((hasDerivAt_id x).add_const T).div_const (2 * T)
  convert (slope_hasDerivAt _).comp x ha using 1
  · rfl
  · simp [div_eq_mul_inv]

lemma smoothPositive_curvature_bound {T : ℝ} (hT : 0 < T) (x : ℝ) :
    0 ≤ curvature ((x + T) / (2 * T)) / (2 * T) ∧
      curvature ((x + T) / (2 * T)) / (2 * T) ≤ 1 / T := by
  have hc := curvature_bounds ((x + T) / (2 * T))
  constructor
  · exact div_nonneg hc.1 (by positivity)
  · apply (div_le_iff₀ (by positivity)).mpr
    have he : 1 / T * (2 * T) = 2 := by field_simp
    rw [he]
    linarith

end LongTails.Proofs.CompactSmoothMaximum
