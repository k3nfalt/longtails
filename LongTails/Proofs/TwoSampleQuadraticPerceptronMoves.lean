import LongTails.Proofs.TwoSampleQuadraticPerceptronBridge

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open LongTails.Setups.TwoSampleQuadraticPerceptron

section Conv

variable {d : ℕ} (D : Data d)

lemma inner_detrended_smooth :
    ⟪detrended d D, smooth d D⟫ = ⟪smooth d D, smooth d D⟫ / 2 := by
  unfold smooth
  simp only [inner_add_left, inner_add_right, inner_shift_shift, real_inner_comm (detrended d D)]
  ring

lemma inner_shift_smooth :
    ⟪shift (detrended d D), smooth d D⟫ = ⟪smooth d D, smooth d D⟫ / 2 := by
  unfold smooth
  simp only [inner_add_left, inner_add_right, inner_shift_shift, real_inner_comm (detrended d D)]
  ring

lemma inner_detrended_rough :
    ⟪detrended d D, rough d D⟫ = ⟪rough d D, rough d D⟫ / 2 := by
  unfold rough
  simp only [inner_sub_left, inner_sub_right, inner_shift_shift, real_inner_comm (detrended d D)]
  ring

lemma inner_shift_rough :
    ⟪shift (detrended d D), rough d D⟫ = -(⟪rough d D, rough d D⟫ / 2) := by
  unfold rough
  simp only [inner_sub_left, inner_sub_right, inner_shift_shift, real_inner_comm (detrended d D)]
  ring

lemma ratio_self_norm (x : Features d) : ⟪x, x⟫ / 2 / ‖x‖ = ‖x‖ / 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [real_inner_self_eq_norm_sq]; field_simp

lemma two_div_sqrt_two : 2 / Real.sqrt 2 = Real.sqrt 2 := by
  rw [div_eq_iff (by positivity)]
  exact (Real.mul_self_sqrt (by norm_num)).symm

lemma inv_sqrt_two_sq : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) = 1 / 2 := by
  rw [div_sqrt_two_mul, one_mul]

lemma sq_mul_inv (x : ℝ) : x ^ 2 * x⁻¹ = x := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · field_simp

lemma sqrt_two_dim_mul (hd : 0 < d) (x : ℝ) :
    Real.sqrt (2 * d) * (x / Real.sqrt d) = Real.sqrt 2 * x := by
  have : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [sqrt_two_mul]
  field_simp

lemma sqrt_two_dim_div : Real.sqrt (2 * d) / Real.sqrt 2 = Real.sqrt d := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  rw [sqrt_two_mul]
  field_simp

lemma dim_div_sqrt (hd : 0 < d) : (d : ℝ) / Real.sqrt d = Real.sqrt d := by
  have : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [div_eq_iff this, Real.mul_self_sqrt (by positivity)]

lemma inner_ones_eq_level (hd : 0 < d) (x : Features d) : ⟪x, ones d⟫ = level d x * d := by
  have : (d : ℝ) ≠ 0 := by positivity
  unfold level
  field_simp

lemma inner_shift_ones_eq_level (hd : 0 < d) (x : Features d) :
    ⟪shift x, ones d⟫ = level d x * d := by
  rw [inner_shift_ones, inner_ones_eq_level hd]

lemma inner_negative_coords (θ : Features d) :
    ⟪D.negative, θ⟫ = level d D.negative * ⟪θ, ones d⟫ + ⟪detrended d D, θ⟫ := by
  conv_lhs => rw [negative_split D]
  rw [inner_add_left, real_inner_smul_left, real_inner_comm θ (ones d)]

lemma inner_shift_negative_coords (θ : Features d) :
    ⟪shift D.negative, θ⟫ =
      level d D.negative * ⟪θ, ones d⟫ + ⟪shift (detrended d D), θ⟫ := by
  conv_lhs => rw [negative_split D]
  rw [shift_add, shift_smul, shift_ones, inner_add_left, real_inner_smul_left,
    real_inner_comm θ (ones d)]

lemma inner_smooth_split (θ : Features d) :
    ⟪detrended d D, θ⟫ + ⟪shift (detrended d D), θ⟫ = ⟪θ, smooth d D⟫ := by
  rw [real_inner_comm (smooth d D) θ]
  unfold smooth
  rw [inner_add_left]

lemma inner_rough_split (θ : Features d) :
    ⟪detrended d D, θ⟫ - ⟪shift (detrended d D), θ⟫ = ⟪θ, rough d D⟫ := by
  rw [real_inner_comm (rough d D) θ]
  unfold rough
  rw [inner_sub_left]

lemma inner_negative_smooth (hd : 0 < d) :
    ⟪D.negative, smooth d D⟫ = ‖smooth d D‖ ^ 2 / 2 := by
  conv_lhs => rw [negative_split D]
  rw [inner_add_left, real_inner_smul_left, real_inner_comm (smooth d D) (ones d),
    inner_smooth_ones D hd, inner_detrended_smooth D, real_inner_self_eq_norm_sq]
  ring

lemma inner_shift_negative_smooth (hd : 0 < d) :
    ⟪shift D.negative, smooth d D⟫ = ‖smooth d D‖ ^ 2 / 2 := by
  conv_lhs => rw [negative_split D]
  rw [shift_add, shift_smul, shift_ones, inner_add_left, real_inner_smul_left,
    real_inner_comm (smooth d D) (ones d), inner_smooth_ones D hd, inner_shift_smooth D,
    real_inner_self_eq_norm_sq]
  ring

lemma inner_negative_rough (hd : 0 < d) :
    ⟪D.negative, rough d D⟫ = ‖rough d D‖ ^ 2 / 2 := by
  conv_lhs => rw [negative_split D]
  rw [inner_add_left, real_inner_smul_left, real_inner_comm (rough d D) (ones d),
    inner_rough_ones D hd, inner_detrended_rough D, real_inner_self_eq_norm_sq]
  ring

lemma inner_shift_negative_rough (hd : 0 < d) :
    ⟪shift D.negative, rough d D⟫ = -(‖rough d D‖ ^ 2 / 2) := by
  conv_lhs => rw [negative_split D]
  rw [shift_add, shift_smul, shift_ones, inner_add_left, real_inner_smul_left,
    real_inner_comm (rough d D) (ones d), inner_rough_ones D hd, inner_shift_rough D,
    real_inner_self_eq_norm_sq]
  ring

lemma norm_div_mul_div (x : Features d) (θ : Features d) (c : ℝ) :
    ‖x‖ / c * (⟪θ, x⟫ / ‖x‖) = ⟪θ, x⟫ / c := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp

end Conv

section Statements

variable {m : Model} {d : ℕ} (D : Data d)

theorem coordinates_first (h : InClass m d D) (θ : Space m d) (γ : ℝ) :
    coordinates m d D (move m d θ γ (direction m d D.positive θ)) =
      ⟨(coordinates m d D θ).p + γ * (eigenvalues m d D).first * (coordinates m d D θ).q,
        (coordinates m d D θ).q + γ * (eigenvalues m d D).first * (coordinates m d D θ).p,
        (coordinates m d D θ).z, (coordinates m d D θ).r, (coordinates m d D θ).y⟩ := by
  cases m with
  | twoLayer =>
      have hp : D.positive ≠ 0 := by
        intro h0; have := h.1; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this
      have hA : ⟪D.positive, axisA d D⟫ = ‖D.positive‖ := by
        conv_lhs => rw [positive_eq D hp]
        rw [real_inner_smul_left, inner_axisA_self D hp, mul_one]
      simp only [coordinates, move, direction, eigenvalues, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul, inner_add_left, real_inner_smul_left, hA,
        inner_positive_axisB D hp]
      congr 1
      · conv_lhs => rw [positive_eq D hp]
        rw [real_inner_smul_right]; ring
      · ring
      · ring
  | conv =>
      obtain ⟨hb1, _, _, hs⟩ := h
      have hd := dimension_pos D hs
      have hp1 : ⟪D.positive, θ.2⟫ = level d D.positive * ⟪θ.2, ones d⟫ := by
        conv_lhs => rw [hb1]
        rw [real_inner_smul_left, real_inner_comm θ.2 (ones d)]
      have hp2 : ⟪shift D.positive, θ.2⟫ = level d D.positive * ⟪θ.2, ones d⟫ := by
        conv_lhs => rw [hb1]
        rw [shift_smul, shift_ones, real_inner_smul_left, real_inner_comm θ.2 (ones d)]
      have po1 := inner_ones_eq_level hd D.positive
      have po2 := inner_shift_ones_eq_level hd D.positive
      have ps1 : ⟪D.positive, smooth d D⟫ = 0 := by
        conv_lhs => rw [hb1]
        rw [real_inner_smul_left, real_inner_comm (smooth d D) (ones d), inner_smooth_ones D hd,
          mul_zero]
      have ps2 : ⟪shift D.positive, smooth d D⟫ = 0 := by
        conv_lhs => rw [hb1]
        rw [shift_smul, shift_ones, real_inner_smul_left, real_inner_comm (smooth d D) (ones d),
          inner_smooth_ones D hd, mul_zero]
      have pr1 : ⟪D.positive, rough d D⟫ = 0 := by
        conv_lhs => rw [hb1]
        rw [real_inner_smul_left, real_inner_comm (rough d D) (ones d), inner_rough_ones D hd,
          mul_zero]
      have pr2 : ⟪shift D.positive, rough d D⟫ = 0 := by
        conv_lhs => rw [hb1]
        rw [shift_smul, shift_ones, real_inner_smul_left, real_inner_comm (rough d D) (ones d),
          inner_rough_ones D hd, mul_zero]
      have T := two_div_sqrt_two
      have f := sqrt_two_dim_mul hd ⟪θ.2, ones d⟫
      have g1 := sqrt_two_dim_div (d := d)
      have g2 := dim_div_sqrt hd
      simp only [coordinates, move, direction, eigenvalues]
      rw [Coordinates.mk.injEq]
      simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        inner_add_left, real_inner_smul_left]
      set L := level d D.positive
      set X := ⟪θ.2, ones d⟫
      set s := Real.sqrt 2
      set t := Real.sqrt (d : ℝ)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · linear_combination (γ / s) * hp1 + (γ / s) * hp2 + (-γ * L) * f + (γ * L * X) * T
      · linear_combination (γ * θ.1.1 / t) * po1 + (γ * θ.1.2 / t) * po2 +
          (γ * (θ.1.1 + θ.1.2) * L) * g2 + (-γ * L * (θ.1.1 + θ.1.2)) * g1
      · linear_combination (γ * θ.1.1 / ‖smooth d D‖) * ps1 + (γ * θ.1.2 / ‖smooth d D‖) * ps2
      · linear_combination (γ / s) * hp1 - (γ / s) * hp2
      · linear_combination (γ * θ.1.1 / ‖rough d D‖) * pr1 + (γ * θ.1.2 / ‖rough d D‖) * pr2

theorem coordinates_second (h : InClass m d D) (θ : Space m d) (γ : ℝ) :
    coordinates m d D (move m d θ γ (negate m d (direction m d D.negative θ))) =
      ⟨(coordinates m d D θ).p - γ * ((eigenvalues m d D).second * (coordinates m d D θ).q +
          (eigenvalues m d D).coupling * (coordinates m d D θ).z),
        (coordinates m d D θ).q - γ * (eigenvalues m d D).second * (coordinates m d D θ).p,
        (coordinates m d D θ).z - γ * (eigenvalues m d D).coupling * (coordinates m d D θ).p,
        (coordinates m d D θ).r - γ * (eigenvalues m d D).slow * (coordinates m d D θ).y,
        (coordinates m d D θ).y - γ * (eigenvalues m d D).slow * (coordinates m d D θ).r⟩ := by
  cases m with
  | twoLayer =>
      simp only [coordinates, move, negate, direction, eigenvalues, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul, smul_neg,
        inner_add_left, inner_neg_left, real_inner_smul_left, inner_negative_axisB D]
      congr 1
      · conv_lhs => rw [negative_eq D]
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
      · ring
      · ring
      · ring
      · ring
  | conv =>
      obtain ⟨_, _, _, hs⟩ := h
      have hd := dimension_pos D hs
      have hsn : ‖smooth d D‖ ≠ 0 := norm_ne_zero_iff.mpr hs
      have hn1 := inner_negative_coords D θ.2
      have hn2 := inner_shift_negative_coords D θ.2
      have hsm := inner_smooth_split D θ.2
      have hrm := inner_rough_split D θ.2
      have o1 := inner_ones_eq_level hd D.negative
      have o2 := inner_shift_ones_eq_level hd D.negative
      have s1 := inner_negative_smooth D hd
      have s2 := inner_shift_negative_smooth D hd
      have r1 := inner_negative_rough D hd
      have r2 := inner_shift_negative_rough D hd
      have u := norm_div_mul_div (smooth d D) θ.2 (Real.sqrt 2)
      have um := norm_div_mul_div (rough d D) θ.2 (Real.sqrt 2)
      have T := two_div_sqrt_two
      have h22 := inv_sqrt_two_sq
      have f := sqrt_two_dim_mul hd ⟪θ.2, ones d⟫
      have g1 := sqrt_two_dim_div (d := d)
      have g2 := dim_div_sqrt hd
      have wn := sq_mul_inv ‖smooth d D‖
      have wm := sq_mul_inv ‖rough d D‖
      simp only [coordinates, move, negate, direction, eigenvalues]
      rw [Coordinates.mk.injEq]
      simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg,
        Prod.snd_neg, smul_eq_mul, smul_neg, inner_add_left, inner_neg_left,
        real_inner_smul_left]
      set L := level d D.negative
      set X := ⟪θ.2, ones d⟫
      set s := Real.sqrt 2
      set t := Real.sqrt (d : ℝ)
      set n := ‖smooth d D‖
      set k := ‖rough d D‖
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · linear_combination (-γ / s) * hn1 + (-γ / s) * hn2 + (-γ / s) * hsm + γ * u +
          (γ * L) * f + (-γ * L * X) * T
      · linear_combination (-γ * θ.1.1 / t) * o1 + (-γ * θ.1.2 / t) * o2 +
          (-γ * (θ.1.1 + θ.1.2) * L) * g2 + (γ * L * (θ.1.1 + θ.1.2)) * g1
      · linear_combination (-γ * θ.1.1 / n) * s1 + (-γ * θ.1.2 / n) * s2 +
          (-γ * (θ.1.1 + θ.1.2) / 2) * wn + (γ * n * (θ.1.1 + θ.1.2)) * h22
      · linear_combination (-γ / s) * hn1 + (γ / s) * hn2 + (-γ / s) * hrm + γ * um
      · linear_combination (-γ * θ.1.1 / k) * r1 + (-γ * θ.1.2 / k) * r2 +
          (-γ * (θ.1.1 - θ.1.2) / 2) * wm + (γ * k * (θ.1.1 - θ.1.2)) * h22

end Statements

end LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
