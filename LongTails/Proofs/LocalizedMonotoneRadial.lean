import LongTails.Proofs.LocalizedMonotoneProfile
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace LongTails.Proofs.LocalizedMonotoneRadial

open LocalizedMonotoneProfile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radial (b : ℝ) (x : E) : E :=
  if ‖x‖ ≤ b then x else (radialRadius b ‖x‖ / ‖x‖) • x

lemma radial_eq_self (b : ℝ) (x : E) (hx : ‖x‖ ≤ b) : radial b x = x := by
  simp only [radial, ite_eq_left hx]

lemma radial_zero (b : ℝ) (hb : 0 ≤ b) : radial b (0 : E) = 0 := by
  exact radial_eq_self b 0 (by simpa using hb)

lemma radial_eq_smul (b : ℝ) (hb : 0 < b) (x : E) (hx : x ≠ 0) :
    radial b x = (radialRadius b ‖x‖ / ‖x‖) • x := by
  unfold radial
  split_ifs with h
  · rw [(radial_identity b ‖x‖ hb h).1, div_self (norm_ne_zero_iff.mpr hx), one_smul]
  · rfl

lemma radial_norm (b : ℝ) (hb : 0 < b) (x : E) :
    ‖radial b x‖ = radialRadius b ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [radial_zero b hb.le, norm_zero, (radial_identity b 0 hb hb.le).1]
  · rw [radial_eq_smul b hb x hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (radial_bounds b ‖x‖ hb (norm_nonneg x)).1 (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

lemma radial_bounded (b : ℝ) (hb : 0 < b) (x : E) : ‖radial b x‖ ≤ 3 * b / 2 := by
  rw [radial_norm b hb]
  exact (radial_bounds b ‖x‖ hb (norm_nonneg x)).2.2

lemma radial_contraction_factor (b : ℝ) (hb : 0 < b) (x : E) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ radial b x = t • x := by
  by_cases hx : x = 0
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    simp only [hx, radial_zero b hb.le, smul_zero]
  · refine ⟨radialRadius b ‖x‖ / ‖x‖,
      div_nonneg (radial_bounds b ‖x‖ hb (norm_nonneg x)).1 (norm_nonneg x), ?_,
      radial_eq_smul b hb x hx⟩
    exact (div_le_one (norm_pos_iff.mpr hx)).mpr (radial_bounds b ‖x‖ hb (norm_nonneg x)).2.1

lemma norm_hasFDerivAt (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  convert h using 1
  · funext y
    rw [Real.sqrt_sq (norm_nonneg y)]
  · rw [Real.sqrt_sq (norm_nonneg x)]
    ext y
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    field_simp
    ring

lemma radial_hasFDerivAt_inside (b : ℝ) (x : E) (hx : ‖x‖ < b) :
    HasFDerivAt (radial b) (ContinuousLinearMap.id ℝ E) x := by
  apply (hasFDerivAt_id x).congr_of_eventuallyEq
  have h : ∀ᶠ y in nhds x, ‖y‖ < b :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx
  filter_upwards [h] with y hy
  exact radial_eq_self b y hy.le

noncomputable def radialJacobian (b : ℝ) (x : E) : E →L[ℝ] E := by
  classical
  exact if x = 0 then ContinuousLinearMap.id ℝ E else
    (radialRadius b ‖x‖ / ‖x‖) • ContinuousLinearMap.id ℝ E +
      ((radialSlope b ‖x‖ - radialRadius b ‖x‖ / ‖x‖) / ‖x‖ ^ 2) •
        InnerProductSpace.rankOne ℝ x x

lemma radial_hasFDerivAt_nonzero (b : ℝ) (hb : 0 < b) (x : E) (hx : x ≠ 0) :
    HasFDerivAt (radial b) (radialJacobian b x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hs := (radial_hasDerivAt b ‖x‖ hb).div (hasDerivAt_id ‖x‖) hn
  have h := (hs.comp_hasFDerivAt x (norm_hasFDerivAt x hx)).smul (hasFDerivAt_id x)
  convert h using 1
  · funext y
    by_cases hy : y = 0
    · subst y
      simp [radial_zero b hb.le]
    · exact radial_eq_smul b hb y hy
  · ext y
    simp only [radialJacobian, ite_eq_right hx, add_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      InnerProductSpace.rankOne_apply, ContinuousLinearMap.smulRight_apply,
      Function.comp_apply, Pi.div_apply, id_eq, mul_one, smul_eq_mul, smul_smul,
      innerSL_apply_apply]
    congr 1
    congr 1
    field_simp

lemma norm_split_scale_le (u z : E) (hu : ‖u‖ = 1) (q r : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖q • z + ((r - q) * inner ℝ u z) • u‖ ≤ ‖z‖ := by
  have hi : (inner ℝ u z) ^ 2 ≤ ‖z‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u z
    rw [hu, one_mul, Real.norm_eq_abs] at h
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have he : ‖q • z + ((r - q) * inner ℝ u z) • u‖ ^ 2 =
      q ^ 2 * (‖z‖ ^ 2 - (inner ℝ u z) ^ 2) + r ^ 2 * (inner ℝ u z) ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, mul_one,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm z u]
    ring
  have h1 := mul_nonneg (sub_nonneg.mpr hq2) (sub_nonneg.mpr hi)
  have h2 := mul_nonneg (sub_nonneg.mpr hr2) (sq_nonneg (inner ℝ u z))
  nlinarith [norm_nonneg (q • z + ((r - q) * inner ℝ u z) • u), norm_nonneg z]

lemma radial_hasFDerivAt (b : ℝ) (hb : 0 < b) (x : E) :
    HasFDerivAt (radial b) (radialJacobian b x) x := by
  classical
  by_cases hx : x = 0
  · subst x
    simpa [radialJacobian] using
      radial_hasFDerivAt_inside b (0 : E) (by simpa using hb)
  · exact radial_hasFDerivAt_nonzero b hb x hx

lemma radialJacobian_apply_le (b : ℝ) (hb : 0 < b) (x z : E) :
    ‖radialJacobian b x z‖ ≤ ‖z‖ := by
  classical
  by_cases hx : x = 0
  · simp [hx, radialJacobian]
  · have hn := norm_pos_iff.mpr hx
    let u := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, hn.ne']
    have hq := radial_bounds b ‖x‖ hb (norm_nonneg x)
    have h := norm_split_scale_le u z hu (radialRadius b ‖x‖ / ‖x‖)
      (radialSlope b ‖x‖) (div_nonneg hq.1 hn.le) ((div_le_one hn).mpr hq.2.1)
      (radialSlope_bounds b ‖x‖).1 (radialSlope_bounds b ‖x‖).2
    convert h using 1
    congr 1
    simp only [radialJacobian, ite_eq_right hx, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply,
      u, real_inner_smul_left, smul_smul]
    congr 1
    congr 1
    field_simp

lemma radialJacobian_norm_le (b : ℝ) (hb : 0 < b) (x : E) :
    ‖radialJacobian b x‖ ≤ 1 := by
  apply (radialJacobian b x).opNorm_le_bound (by norm_num)
  intro z
  simpa only [one_mul] using radialJacobian_apply_le b hb x z

lemma radial_nonexpansive (b : ℝ) (hb : 0 < b) (x y : E) :
    ‖radial b x - radial b y‖ ≤ ‖x - y‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (radial_hasFDerivAt b hb z).hasFDerivWithinAt)
    (fun z _ => radialJacobian_norm_le b hb z) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [one_mul] using h

lemma unit_rankOne_difference (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖InnerProductSpace.rankOne ℝ u u - InnerProductSpace.rankOne ℝ v v‖ ≤ 2 * ‖u - v‖ := by
  have he : InnerProductSpace.rankOne ℝ u u - InnerProductSpace.rankOne ℝ v v =
      InnerProductSpace.rankOne ℝ (u - v) u + InnerProductSpace.rankOne ℝ v (u - v) := by
    ext z
    simp only [sub_apply, add_apply, InnerProductSpace.rankOne_apply, inner_sub_left]
    module
  rw [he]
  calc
    _ ≤ ‖InnerProductSpace.rankOne ℝ (u - v) u‖ +
        ‖InnerProductSpace.rankOne ℝ v (u - v)‖ := norm_add_le _ _
    _ = _ := by rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne, hu, hv]; ring

lemma normalized_difference (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 / ‖x‖ * ‖x - y‖ := by
  have hr := norm_pos_iff.mpr hx
  have hs := norm_pos_iff.mpr hy
  have he : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by module
  have hc : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    have hh : ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by field_simp
    rw [hh, abs_div, abs_of_pos (mul_pos hr hs)]
    field_simp
  have hn : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
  rw [he]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hc]
      simp [abs_of_pos hr, div_eq_mul_inv, mul_comm]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hn hr.le)
    _ = _ := by ring

lemma radius_ratio_difference (b r s : ℝ) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s) :
    |radialRadius b r / r - radialRadius b s / s| ≤ 2 / r * |r - s| := by
  have he : radialRadius b r / r - radialRadius b s / s =
      (radialRadius b r - radialRadius b s) / r +
        (s - r) / (r * s) * radialRadius b s := by field_simp; ring
  have hp := radial_bounds b s hb hs.le
  rw [he]
  calc
    _ ≤ |(radialRadius b r - radialRadius b s) / r| +
        |(s - r) / (r * s) * radialRadius b s| := abs_add_le _ _
    _ = |radialRadius b r - radialRadius b s| / r +
        |r - s| / (r * s) * radialRadius b s := by
      rw [abs_div, abs_of_pos hr, abs_mul, abs_div, abs_of_pos (mul_pos hr hs),
        abs_of_nonneg hp.1, abs_sub_comm s r]
    _ ≤ |r - s| / r + |r - s| / (r * s) * s :=
      add_le_add (div_le_div_of_nonneg_right (radial_difference b r s hb) hr.le)
        (mul_le_mul_of_nonneg_left hp.2.1 (by positivity))
    _ = _ := by field_simp; ring

lemma radialJacobian_inside (b : ℝ) (hb : 0 < b) (x : E) (hx : ‖x‖ ≤ b) :
    radialJacobian b x = ContinuousLinearMap.id ℝ E := by
  classical
  by_cases hz : x = 0
  · simp [hz, radialJacobian]
  · have h := radial_identity b ‖x‖ hb hx
    simp [radialJacobian, hz, h.1, h.2, norm_ne_zero_iff.mpr hz]

lemma radialJacobian_unit_form (b : ℝ) (x : E) (hx : x ≠ 0) :
    radialJacobian b x =
      (radialRadius b ‖x‖ / ‖x‖) • ContinuousLinearMap.id ℝ E +
        (radialSlope b ‖x‖ - radialRadius b ‖x‖ / ‖x‖) •
          InnerProductSpace.rankOne ℝ (‖x‖⁻¹ • x) (‖x‖⁻¹ • x) := by
  classical
  ext z
  simp only [radialJacobian, ite_eq_right hx, add_apply, smul_apply,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, smul_smul]
  congr 1
  congr 1
  field_simp

lemma scaled_inverse_bound (b r t : ℝ) (hb : 0 < b) (hr : 0 < r)
    (hbr : b ≤ 2 * r) (ht : 0 ≤ t) : 2 / r * t ≤ 4 * (t / b) := by
  calc
    2 / r * t = 2 * t / r := by ring
    _ ≤ 4 * t / b := (div_le_div_iff₀ hr hb).mpr (by nlinarith)
    _ = _ := by ring

lemma radialJacobian_difference_outer (b : ℝ) (hb : 0 < b) (x y : E)
    (hx : b / 2 ≤ ‖x‖) (hy : b / 2 ≤ ‖y‖) :
    ‖radialJacobian b x - radialJacobian b y‖ ≤ 32 * (‖x - y‖ / b) := by
  have hr : 0 < ‖x‖ := by linarith
  have hs : 0 < ‖y‖ := by linarith
  have hx0 := norm_pos_iff.mp hr
  have hy0 := norm_pos_iff.mp hs
  let q := radialRadius b ‖x‖ / ‖x‖
  let q' := radialRadius b ‖y‖ / ‖y‖
  let h := radialSlope b ‖x‖ - q
  let h' := radialSlope b ‖y‖ - q'
  let u := ‖x‖⁻¹ • x
  let v := ‖y‖⁻¹ • y
  let U := InnerProductSpace.rankOne ℝ u u
  let V := InnerProductSpace.rankOne ℝ v v
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hr.ne']
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hs.ne']
  have hU : ‖U‖ = 1 := by simp [U, hu]
  have hi : ‖(ContinuousLinearMap.id ℝ E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simp
  have hnorm : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have hq : |q - q'| ≤ 4 * (‖x - y‖ / b) := by
    calc
      _ ≤ 2 / ‖x‖ * |‖x‖ - ‖y‖| := radius_ratio_difference b ‖x‖ ‖y‖ hb hr hs
      _ ≤ 2 / ‖x‖ * ‖x - y‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ _ := scaled_inverse_bound b ‖x‖ ‖x - y‖ hb hr (by linarith) (norm_nonneg _)
  have hh : |h - h'| ≤ 5 * (‖x - y‖ / b) := by
    have hd := radialSlope_difference b ‖x‖ ‖y‖ hb
    have hn := div_le_div_of_nonneg_right hnorm hb.le
    have he : h - h' = (radialSlope b ‖x‖ - radialSlope b ‖y‖) - (q - q') := by
      dsimp [h, h']
      ring
    rw [he]
    have ha := abs_sub (radialSlope b ‖x‖ - radialSlope b ‖y‖) (q - q')
    linarith
  have hh' : |h'| ≤ 1 := by
    have hqb := radial_bounds b ‖y‖ hb hs.le
    have hq0 : 0 ≤ q' := div_nonneg hqb.1 hs.le
    have hq1 : q' ≤ 1 := (div_le_one hs).mpr hqb.2.1
    have hh0 := radialSlope_bounds b ‖y‖
    rw [abs_le]
    dsimp [h']
    constructor <;> linarith
  have huv : ‖u - v‖ ≤ 4 * (‖x - y‖ / b) :=
    (normalized_difference x y hx0 hy0).trans
      (scaled_inverse_bound b ‖x‖ ‖x - y‖ hb hr (by linarith) (norm_nonneg _))
  have hUV : ‖U - V‖ ≤ 8 * (‖x - y‖ / b) := by
    have he := unit_rankOne_difference u v hu hv
    dsimp [U, V]
    linarith
  have he : radialJacobian b x - radialJacobian b y =
      ((q - q') • ContinuousLinearMap.id ℝ E + (h - h') • U) + h' • (U - V) := by
    rw [radialJacobian_unit_form b x hx0, radialJacobian_unit_form b y hy0]
    dsimp [q, q', h, h', U, V, u, v]
    module
  rw [he]
  calc
    _ ≤ (‖(q - q') • ContinuousLinearMap.id ℝ E‖ + ‖(h - h') • U‖) + ‖h' • (U - V)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (|q - q'| * ‖ContinuousLinearMap.id ℝ E‖ + |h - h'|) + |h'| * ‖U - V‖ := by
      simp only [norm_smul, Real.norm_eq_abs, hU, mul_one]
    _ ≤ (4 * (‖x - y‖ / b) + 5 * (‖x - y‖ / b)) + 8 * (‖x - y‖ / b) := by
      have h1 := mul_le_mul hq hi (norm_nonneg _) (by positivity : 0 ≤ 4 * (‖x - y‖ / b))
      have h2 := mul_le_mul hh' hUV (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simp only [mul_one, one_mul] at h1 h2
      linarith
    _ ≤ _ := by nlinarith [div_nonneg (norm_nonneg (x - y)) hb.le]

lemma radialJacobian_difference_near (b : ℝ) (hb : 0 < b) (x y : E)
    (hx : ‖x‖ ≤ b / 2) :
    ‖radialJacobian b x - radialJacobian b y‖ ≤ 32 * (‖x - y‖ / b) := by
  by_cases hy : ‖y‖ ≤ b
  · rw [radialJacobian_inside b hb x (by linarith), radialJacobian_inside b hb y hy,
      sub_self, norm_zero]
    positivity
  · have hd : b / 2 ≤ ‖x - y‖ := by
      have hn := norm_sub_norm_le y x
      rw [norm_sub_rev] at hn
      push Not at hy
      linarith
    have hj : ‖radialJacobian b x - radialJacobian b y‖ ≤ 2 := by
      have h1 := radialJacobian_norm_le b hb x
      have h2 := radialJacobian_norm_le b hb y
      exact (norm_sub_le _ _).trans (by linarith)
    apply hj.trans
    calc
      (2 : ℝ) ≤ 32 * ‖x - y‖ / b := (le_div_iff₀ hb).mpr (by nlinarith)
      _ = _ := by ring

lemma radialJacobian_difference (b : ℝ) (hb : 0 < b) (x y : E) :
    ‖radialJacobian b x - radialJacobian b y‖ ≤ 32 / b * ‖x - y‖ := by
  have h : ‖radialJacobian b x - radialJacobian b y‖ ≤ 32 * (‖x - y‖ / b) := by
    by_cases hx : b / 2 ≤ ‖x‖
    · by_cases hy : b / 2 ≤ ‖y‖
      · exact radialJacobian_difference_outer b hb x y hx hy
      · simpa only [norm_sub_rev] using radialJacobian_difference_near b hb y x (le_of_not_ge hy)
    · exact radialJacobian_difference_near b hb x y (le_of_not_ge hx)
  convert h using 1
  ring

end LongTails.Proofs.LocalizedMonotoneRadial
