import LongTails.Proofs.AdaptivePolynomialHinge
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.InterpolatedFiniteSumProfiles

open AdaptivePolynomialHinge

noncomputable def profile (t : ℝ) : ℝ :=
  (ramp 2 (2 * t - 1 / 2) + ramp 2 (-2 * t - 1 / 2)) / 2

noncomputable def profileSlope (t : ℝ) : ℝ :=
  mixing 2 (2 * t - 1 / 2) - mixing 2 (-2 * t - 1 / 2)

noncomputable def profileCurvature (t : ℝ) : ℝ :=
  2 * (curvature 2 (2 * t - 1 / 2) + curvature 2 (-2 * t - 1 / 2))

lemma profile_hasDerivAt (t : ℝ) : HasDerivAt profile (profileSlope t) t := by
  have hp := (ramp_hasDerivAt 2 (by omega) (2 * t - 1 / 2)).comp t
    (((hasDerivAt_id t).const_mul 2).sub_const (1 / 2))
  have hn := (ramp_hasDerivAt 2 (by omega) (-2 * t - 1 / 2)).comp t
    (((hasDerivAt_id t).const_mul (-2)).sub_const (1 / 2))
  convert (hp.add hn).div_const 2 using 1
  · rfl
  · simp only [profileSlope, mul_one]
    ring

lemma profileSlope_hasDerivAt (t : ℝ) :
    HasDerivAt profileSlope (profileCurvature t) t := by
  have hp := (mixing_hasDerivAt 2 (by omega) (2 * t - 1 / 2)).comp t
    (((hasDerivAt_id t).const_mul 2).sub_const (1 / 2))
  have hn := (mixing_hasDerivAt 2 (by omega) (-2 * t - 1 / 2)).comp t
    (((hasDerivAt_id t).const_mul (-2)).sub_const (1 / 2))
  convert hp.sub hn using 1
  · rfl
  · simp only [profileCurvature, mul_one]
    ring

lemma profile_nonnegative (t : ℝ) : 0 ≤ profile t := by
  exact div_nonneg (add_nonneg (ramp_nonnegative 2 (by omega) _)
    (ramp_nonnegative 2 (by omega) _)) (by norm_num)

lemma profileSlope_bound (t : ℝ) : |profileSlope t| ≤ 1 := by
  have hp := mixing_bounds 2 (2 * t - 1 / 2)
  have hn := mixing_bounds 2 (-2 * t - 1 / 2)
  rw [abs_le]
  dsimp [profileSlope]
  constructor <;> linarith

lemma profileCurvature_nonnegative (t : ℝ) : 0 ≤ profileCurvature t := by
  exact mul_nonneg (by norm_num) (add_nonneg (curvature_bounds 2 (by omega) _).1
    (curvature_bounds 2 (by omega) _).1)

lemma profile_convex : ConvexOn ℝ Set.univ profile := by
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t => (profile_hasDerivAt t).differentiableAt
  · have he : deriv profile = profileSlope := funext fun t => (profile_hasDerivAt t).deriv
    rw [he]
    exact fun t => (profileSlope_hasDerivAt t).differentiableAt
  · intro t
    have he : deriv profile = profileSlope := funext fun t => (profile_hasDerivAt t).deriv
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, he,
      (profileSlope_hasDerivAt t).deriv] using profileCurvature_nonnegative t

lemma profile_flat (t : ℝ) (ht : |t| ≤ 1 / 4) :
    profile t = 0 ∧ profileSlope t = 0 := by
  have hp : 2 * t - 1 / 2 ≤ 0 := by have := (abs_le.mp ht).2; linarith
  have hn : -2 * t - 1 / 2 ≤ 0 := by have := (abs_le.mp ht).1; linarith
  simp only [profile, profileSlope, ramp, mixing, ite_eq_left hp, ite_eq_left hn]
  norm_num

lemma profile_linear (t : ℝ) (ht : 3 / 4 ≤ t) :
    profile t = t - 1 / 2 ∧ profileSlope t = 1 := by
  have hp : ¬2 * t - 1 / 2 ≤ 0 := by linarith
  have hn : -2 * t - 1 / 2 ≤ 0 := by linarith
  by_cases h : 2 * t - 1 / 2 ≤ 1
  · have he : t = 3 / 4 := by linarith
    subst t
    norm_num [profile, profileSlope, ramp, mixing, primitive, weight]
  · simp only [profile, profileSlope, ramp, mixing, ite_eq_right hp, ite_eq_left hn,
      ite_eq_right h]
    constructor
    · norm_num
      ring
    · norm_num

lemma curvature_two_bound (t : ℝ) : curvature 2 t ≤ 3 / 2 := by
  unfold curvature
  split_ifs with h h'
  · norm_num
  · norm_num [AdaptivePolynomialHinge.slope]
    nlinarith [sq_nonneg (t - 1 / 2)]
  · norm_num

lemma profileCurvature_bound (t : ℝ) : profileCurvature t ≤ 3 := by
  by_cases ht : 0 ≤ t
  · have hn : -2 * t - 1 / 2 ≤ 0 := by linarith
    have hb := curvature_two_bound (2 * t - 1 / 2)
    simp only [profileCurvature, curvature, ite_eq_left hn]
    change 2 * (curvature 2 (2 * t - 1 / 2) + 0) ≤ 3
    linarith
  · have hp : 2 * t - 1 / 2 ≤ 0 := by linarith
    have hb := curvature_two_bound (-2 * t - 1 / 2)
    simp only [profileCurvature, curvature, ite_eq_left hp]
    change 2 * (0 + curvature 2 (-2 * t - 1 / 2)) ≤ 3
    linarith

lemma profile_even (t : ℝ) : profile (-t) = profile t := by
  simp only [profile, mul_neg, neg_mul, neg_neg, add_comm]

lemma ramp_two_above_linear (t : ℝ) : t - 1 / 2 ≤ ramp 2 t := by
  unfold ramp
  split_ifs with h h'
  · linarith
  · norm_num [primitive]
    have hp := mul_nonneg (pow_nonneg (sub_nonneg.mpr h') 3)
      (show 0 ≤ 1 + t by linarith)
    nlinarith
  · norm_num

lemma ramp_two_linear (t : ℝ) (ht : 1 ≤ t) : ramp 2 t = t - 1 / 2 := by
  have hp : ¬t ≤ 0 := by linarith
  by_cases h : t ≤ 1
  · have he : t = 1 := le_antisymm h ht
    subst t
    norm_num [ramp, primitive]
  · simp only [ramp, ite_eq_right hp, ite_eq_right h]
    norm_num

noncomputable def smoothMax (W a b : ℝ) : ℝ :=
  a + W * ramp 2 ((b - a) / W + 1 / 2)

lemma smoothMax_above (W a b : ℝ) (hW : 0 < W) :
    a ≤ smoothMax W a b ∧ b ≤ smoothMax W a b := by
  have hp := mul_nonneg hW.le (ramp_nonnegative 2 (by omega) ((b - a) / W + 1 / 2))
  have hl := mul_le_mul_of_nonneg_left (ramp_two_above_linear ((b - a) / W + 1 / 2)) hW.le
  have he : W * (((b - a) / W + 1 / 2) - 1 / 2) = b - a := by
    field_simp
    ring
  rw [he] at hl
  dsimp [smoothMax]
  constructor <;> linarith

lemma smoothMax_left (W a b : ℝ) (hW : 0 < W) (h : b + W / 2 ≤ a) :
    smoothMax W a b = a := by
  have ht : (b - a) / W + 1 / 2 ≤ 0 := by
    have hh : (b - a) / W ≤ -(1 / 2) := (div_le_iff₀ hW).mpr (by linarith)
    linarith
  simp only [smoothMax, ramp, ite_eq_left ht, mul_zero, add_zero]

lemma smoothMax_right (W a b : ℝ) (hW : 0 < W) (h : a + W / 2 ≤ b) :
    smoothMax W a b = b := by
  have ht : 1 ≤ (b - a) / W + 1 / 2 := by
    have hh : 1 / 2 ≤ (b - a) / W := (le_div_iff₀ hW).mpr (by linarith)
    linarith
  rw [smoothMax, ramp_two_linear _ ht]
  field_simp
  ring

lemma profileSlope_lipschitz (x y : ℝ) : |profileSlope x - profileSlope y| ≤ 3 * |x - y| := by
  have hl : LipschitzWith (3 : NNReal) profileSlope := lipschitzWith_of_nnnorm_deriv_le
    (fun t => (profileSlope_hasDerivAt t).differentiableAt) (fun t => by
      change ‖deriv profileSlope t‖ ≤ (3 : ℝ)
      rw [(profileSlope_hasDerivAt t).deriv, Real.norm_eq_abs,
        abs_of_nonneg (profileCurvature_nonnegative t)]
      exact profileCurvature_bound t)
  simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using hl.norm_sub_le x y

lemma profile_remainder (x y : ℝ) :
    0 ≤ profile y - profile x - profileSlope x * (y - x) ∧
      profile y - profile x - profileSlope x * (y - x) ≤ 3 / 2 * (y - x) ^ 2 := by
  have hg (t : ℝ) : HasGradientAt profile (profileSlope t) t := by
    simpa using (profile_hasDerivAt t).hasGradientAt
  have hl (u v : ℝ) : ‖profileSlope u - profileSlope v‖ ≤ 3 * ‖u - v‖ := by
    simpa only [Real.norm_eq_abs] using profileSlope_lipschitz u v
  have hs := OracleTemplate.Gradient.convex_support profile_convex hg x y
  have hu := OracleTemplate.Gradient.smooth_upper_bound hg hl x y
  simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs] at hs hu
  constructor <;> linarith

end LongTails.Proofs.InterpolatedFiniteSumProfiles
