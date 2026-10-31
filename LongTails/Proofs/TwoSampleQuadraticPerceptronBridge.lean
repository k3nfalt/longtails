import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open LongTails.Setups.TwoSampleQuadraticPerceptron

section Conv

variable {d : ℕ} (D : Data d)

lemma dimension_pos (h : smooth d D ≠ 0) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; exact absurd (Subsingleton.elim _ _) h
  · exact hd

lemma inner_detrended_ones (hd : 0 < d) : ⟪detrended d D, ones d⟫ = 0 := by
  unfold detrended level
  rw [inner_sub_left, real_inner_smul_left, inner_ones_ones]
  have : (d : ℝ) ≠ 0 := by positivity
  field_simp; ring

lemma negative_split : D.negative = level d D.negative • ones d + detrended d D := by
  unfold detrended; abel

lemma inner_smooth_ones (hd : 0 < d) : ⟪smooth d D, ones d⟫ = 0 := by
  unfold smooth
  rw [inner_add_left, inner_shift_ones, inner_detrended_ones D hd, add_zero]

lemma inner_rough_ones (hd : 0 < d) : ⟪rough d D, ones d⟫ = 0 := by
  unfold rough
  rw [inner_sub_left, inner_shift_ones, inner_detrended_ones D hd, sub_zero]

lemma div_sqrt_two_mul (x y : ℝ) : x / Real.sqrt 2 * (y / Real.sqrt 2) = x * y / 2 := by
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma sqrt_two_mul (d : ℕ) : Real.sqrt (2 * d) = Real.sqrt 2 * Real.sqrt d := by
  rw [Real.sqrt_mul (by norm_num)]

end Conv

section Statements

variable {m : Model} {d : ℕ} (D : Data d)

theorem margin_positive (h : InClass m d D) (θ : Space m d) :
    margin m d D.positive θ = (eigenvalues m d D).first * (coordinates m d D θ).p *
      (coordinates m d D θ).q := by
  cases m with
  | twoLayer =>
      have hp : D.positive ≠ 0 := by
        intro h0; have := h.1; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this
      simp only [margin, coordinates, eigenvalues]
      conv_lhs => rw [positive_eq D hp]
      rw [real_inner_smul_right]; ring
  | conv =>
      obtain ⟨hb1, _, _, hs⟩ := h
      have hd := dimension_pos D hs
      have hd' : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
      have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
      have hp1 : ⟪D.positive, θ.2⟫ = level d D.positive * ⟪ones d, θ.2⟫ := by
        conv_lhs => rw [hb1]
        rw [real_inner_smul_left]
      have hp2 : ⟪shift D.positive, θ.2⟫ = level d D.positive * ⟪ones d, θ.2⟫ := by
        conv_lhs => rw [hb1]
        rw [shift_smul, shift_ones, real_inner_smul_left]
      have t1 : level d D.positive * Real.sqrt (2 * d) * ((θ.1.1 + θ.1.2) / Real.sqrt 2) *
          (⟪θ.2, ones d⟫ / Real.sqrt d) = level d D.positive * (θ.1.1 + θ.1.2) * ⟪ones d, θ.2⟫ := by
        rw [sqrt_two_mul, real_inner_comm θ.2 (ones d)]
        field_simp
      simp only [margin, coordinates, eigenvalues]
      linear_combination θ.1.1 * hp1 + θ.1.2 * hp2 - t1

theorem margin_negative (h : InClass m d D) (θ : Space m d) :
    margin m d D.negative θ = (eigenvalues m d D).second * (coordinates m d D θ).p *
        (coordinates m d D θ).q +
      (eigenvalues m d D).coupling * (coordinates m d D θ).p * (coordinates m d D θ).z +
      (eigenvalues m d D).slow * (coordinates m d D θ).r * (coordinates m d D θ).y := by
  cases m with
  | twoLayer =>
      simp only [margin, coordinates, eigenvalues]
      conv_lhs => rw [negative_eq D]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
  | conv =>
      obtain ⟨_, _, _, hs⟩ := h
      have hd := dimension_pos D hs
      have hd' : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
      have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
      have hsm := inner_eq_norm_mul_coord (smooth d D) θ.2
      have hro := inner_eq_norm_mul_coord (rough d D) θ.2
      simp only [margin, coordinates, eigenvalues]
      rw [div_sqrt_two_mul, div_sqrt_two_mul]
      set Ks := ⟪θ.2, smooth d D⟫ / ‖smooth d D‖
      set Kr := ⟪θ.2, rough d D⟫ / ‖rough d D‖
      have hs1 : ⟪smooth d D, θ.2⟫ = ⟪detrended d D, θ.2⟫ + ⟪shift (detrended d D), θ.2⟫ := by
        unfold smooth; rw [inner_add_left]
      have hr1 : ⟪rough d D, θ.2⟫ = ⟪detrended d D, θ.2⟫ - ⟪shift (detrended d D), θ.2⟫ := by
        unfold rough; rw [inner_sub_left]
      rw [hs1] at hsm
      rw [hr1] at hro
      have hn1 : ⟪D.negative, θ.2⟫ =
          level d D.negative * ⟪ones d, θ.2⟫ + ⟪detrended d D, θ.2⟫ := by
        conv_lhs => rw [negative_split D]
        rw [inner_add_left, real_inner_smul_left]
      have hn2 : ⟪shift D.negative, θ.2⟫ =
          level d D.negative * ⟪ones d, θ.2⟫ + ⟪shift (detrended d D), θ.2⟫ := by
        conv_lhs => rw [negative_split D]
        rw [shift_add, shift_smul, shift_ones, inner_add_left, real_inner_smul_left]
      have t1 : level d D.negative * Real.sqrt (2 * d) * ((θ.1.1 + θ.1.2) / Real.sqrt 2) *
          (⟪θ.2, ones d⟫ / Real.sqrt d) = level d D.negative * (θ.1.1 + θ.1.2) * ⟪ones d, θ.2⟫ := by
        rw [sqrt_two_mul, real_inner_comm θ.2 (ones d)]
        field_simp
      linear_combination θ.1.1 * hn1 + θ.1.2 * hn2 - t1 + (θ.1.1 + θ.1.2) / 2 * hsm +
        (θ.1.1 - θ.1.2) / 2 * hro

end Statements

end LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
