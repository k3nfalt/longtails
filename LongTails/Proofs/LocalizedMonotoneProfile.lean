import LongTails.Proofs.SmoothConvexFiniteGeometry
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

namespace LongTails.Proofs.LocalizedMonotoneProfile

open SmoothConvexFiniteGeometry

noncomputable def profile (a x : ℝ) : ℝ :=
  a * (ramp (x / a - 1) - ramp (-x / a - 1))

noncomputable def slope (a x : ℝ) : ℝ :=
  rampSlope (x / a - 1) + rampSlope (-x / a - 1)

lemma profile_neg (a x : ℝ) : profile a (-x) = -profile a x := by
  simp only [profile, neg_neg]
  ring

lemma profile_flat (a x : ℝ) (ha : 0 < a) (hx : |x| ≤ a) :
    profile a x = 0 ∧ slope a x = 0 := by
  have hp : x / a - 1 ≤ 0 := by
    have := (div_le_one ha).mpr (abs_le.mp hx).2
    linarith
  have hn : -x / a - 1 ≤ 0 := by
    have := (div_le_one ha).mpr (show -x ≤ a by linarith [(abs_le.mp hx).1])
    linarith
  simp [profile, slope, ramp, rampSlope_cases, hp, hn]

lemma profile_hasDerivAt (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (profile a) (slope a x) x := by
  have hp : HasDerivAt (fun y : ℝ => y / a - 1) (1 / a) x := by
    simpa using ((hasDerivAt_id x).div_const a).sub_const 1
  have hn : HasDerivAt (fun y : ℝ => -y / a - 1) (-1 / a) x := by
    simpa using (((hasDerivAt_id x).neg).div_const a).sub_const 1
  have h := (((ramp_hasDerivAt _).comp x hp).sub
    ((ramp_hasDerivAt _).comp x hn)).const_mul a
  convert h using 1
  · rfl
  · dsimp [slope]
    field_simp
    ring

lemma slope_nonneg (a x : ℝ) : 0 ≤ slope a x :=
  add_nonneg (rampSlope_nonneg _) (rampSlope_nonneg _)

lemma slope_le_one (a x : ℝ) : slope a x ≤ 1 := by
  have h : x / a - 1 ≤ 0 ∨ -x / a - 1 ≤ 0 := by
    rw [neg_div]
    by_contra h
    push Not at h
    linarith
  rcases h with h | h
  · simp only [slope, rampSlope_cases, ite_eq_left h, zero_add]
    split_ifs <;> linarith
  · simp only [slope, rampSlope_cases, ite_eq_left h, add_zero]
    split_ifs <;> linarith

lemma slope_difference (a x y : ℝ) (ha : 0 < a) :
    |slope a x - slope a y| ≤ 2 / a * |x - y| := by
  have hp := rampSlope_lipschitz (x / a - 1) (y / a - 1)
  have hn := rampSlope_lipschitz (-x / a - 1) (-y / a - 1)
  have ep : x / a - 1 - (y / a - 1) = (x - y) / a := by ring
  have en : -x / a - 1 - (-y / a - 1) = -(x - y) / a := by ring
  rw [ep, abs_div, abs_of_pos ha] at hp
  rw [en, abs_div, abs_neg, abs_of_pos ha] at hn
  calc
    |slope a x - slope a y| =
        |(rampSlope (x / a - 1) - rampSlope (y / a - 1)) +
          (rampSlope (-x / a - 1) - rampSlope (-y / a - 1))| := by
      congr 1
      dsimp [slope]
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 / a * |x - y| := by
      calc
        _ ≤ |x - y| / a + |x - y| / a := add_le_add hp hn
        _ = _ := by ring

lemma base_profile_gap (x : ℝ) :
    |x - (ramp (x - 1) - ramp (-x - 1))| ≤ 3 / 2 := by
  rw [abs_le]
  simp only [ramp]
  split_ifs <;> constructor <;>
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2),
      sq_nonneg (x - 1), sq_nonneg (x + 1)]

lemma profile_gap (a x : ℝ) (ha : 0 < a) :
    |x - profile a x| ≤ 3 * a / 2 := by
  have h := mul_le_mul_of_nonneg_left (base_profile_gap (x / a)) ha.le
  have he : x - profile a x =
      a * (x / a - (ramp (x / a - 1) - ramp (-(x / a) - 1))) := by
    dsimp [profile]
    rw [neg_div]
    field_simp
  rw [he, abs_mul, abs_of_pos ha]
  linarith

lemma profile_affine (a x : ℝ) (ha : 0 < a) (hx : 2 * a ≤ x) :
    profile a x = x - 3 * a / 2 := by
  have hp : 1 ≤ x / a - 1 := by
    have := (le_div_iff₀ ha).mpr hx
    linarith
  have hn : -x / a - 1 ≤ 0 := by
    rw [neg_div]
    linarith
  have he : ramp (x / a - 1) = x / a - 1 - 1 / 2 := by
    simp only [ramp]
    split_ifs <;> nlinarith
  have hz : ramp (-x / a - 1) = 0 := by simp only [ramp, ite_eq_left hn]
  rw [profile, he, hz, sub_zero]
  field_simp
  ring

noncomputable def radialRadius (b r : ℝ) : ℝ := r - b * ramp (r / b - 1)

noncomputable def radialSlope (b r : ℝ) : ℝ := 1 - rampSlope (r / b - 1)

lemma radial_hasDerivAt (b r : ℝ) (hb : 0 < b) :
    HasDerivAt (radialRadius b) (radialSlope b r) r := by
  have hi : HasDerivAt (fun s : ℝ => s / b - 1) (1 / b) r := by
    simpa using ((hasDerivAt_id r).div_const b).sub_const 1
  have h := (hasDerivAt_id r).sub (((ramp_hasDerivAt _).comp r hi).const_mul b)
  convert h using 1
  · rfl
  · dsimp [radialSlope]
    field_simp

lemma radialSlope_bounds (b r : ℝ) : 0 ≤ radialSlope b r ∧ radialSlope b r ≤ 1 := by
  dsimp [radialSlope]
  constructor <;> linarith [rampSlope_nonneg (r / b - 1), rampSlope_le_one (r / b - 1)]

lemma radialSlope_difference (b r s : ℝ) (hb : 0 < b) :
    |radialSlope b r - radialSlope b s| ≤ |r - s| / b := by
  have h := rampSlope_lipschitz (r / b - 1) (s / b - 1)
  have he : r / b - 1 - (s / b - 1) = (r - s) / b := by ring
  rw [he, abs_div, abs_of_pos hb] at h
  simpa only [radialSlope, sub_sub_sub_cancel_left, abs_sub_comm] using h

lemma radial_identity (b r : ℝ) (hb : 0 < b) (hr : r ≤ b) :
    radialRadius b r = r ∧ radialSlope b r = 1 := by
  have h : r / b - 1 ≤ 0 := by linarith [(div_le_one hb).mpr hr]
  simp [radialRadius, radialSlope, ramp, rampSlope_cases, h]

lemma radial_constant (b r : ℝ) (hb : 0 < b) (hr : 2 * b ≤ r) :
    radialRadius b r = 3 * b / 2 ∧ radialSlope b r = 0 := by
  have ht : 1 ≤ r / b - 1 := by
    have := (le_div_iff₀ hb).mpr hr
    linarith
  have he : ramp (r / b - 1) = r / b - 1 - 1 / 2 := by
    simp only [ramp]
    split_ifs <;> nlinarith
  constructor
  · simp only [radialRadius, he]
    field_simp
    ring
  · simp only [radialSlope, rampSlope_cases]
    split_ifs <;> linarith

lemma profile_monotone (a : ℝ) (ha : 0 < a) : Monotone (profile a) := by
  apply monotone_of_deriv_nonneg (fun x => (profile_hasDerivAt a x ha).differentiableAt)
  intro x
  rw [(profile_hasDerivAt a x ha).deriv]
  exact slope_nonneg a x

lemma profile_difference (a x y : ℝ) (ha : 0 < a) :
    |profile a x - profile a y| ≤ |x - y| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (profile_hasDerivAt a z ha).hasDerivWithinAt)
    (fun z _ => show ‖slope a z‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg (slope_nonneg a z)]
      exact slope_le_one a z) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

lemma radial_monotone (b : ℝ) (hb : 0 < b) : Monotone (radialRadius b) := by
  apply monotone_of_deriv_nonneg (fun x => (radial_hasDerivAt b x hb).differentiableAt)
  intro x
  rw [(radial_hasDerivAt b x hb).deriv]
  exact (radialSlope_bounds b x).1

lemma radial_difference (b r s : ℝ) (hb : 0 < b) :
    |radialRadius b r - radialRadius b s| ≤ |r - s| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (radial_hasDerivAt b z hb).hasDerivWithinAt)
    (fun z _ => show ‖radialSlope b z‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg (radialSlope_bounds b z).1]
      exact (radialSlope_bounds b z).2) (Set.mem_univ s) (Set.mem_univ r)
  simpa only [Real.norm_eq_abs, one_mul] using h

lemma radial_bounds (b r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) :
    0 ≤ radialRadius b r ∧ radialRadius b r ≤ r ∧ radialRadius b r ≤ 3 * b / 2 := by
  have hzero := (radial_identity b 0 hb hb.le).1
  have hnonneg : 0 ≤ radialRadius b r := by
    simpa only [hzero] using radial_monotone b hb hr
  have hle : radialRadius b r ≤ r := by
    have h := radial_difference b r 0 hb
    simpa only [hzero, sub_zero, abs_of_nonneg hnonneg, abs_of_nonneg hr] using h
  refine ⟨hnonneg, hle, ?_⟩
  rcases le_total r (2 * b) with h | h
  · have hm := radial_monotone b hb h
    simpa only [(radial_constant b (2 * b) hb le_rfl).1] using hm
  · exact (radial_constant b r hb h).1.le

end LongTails.Proofs.LocalizedMonotoneProfile
