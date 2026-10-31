import LongTails.Algorithms.CompositeGapAccelerated
import Mathlib.Tactic

namespace LongTails.Proofs.CompositeGapTuning

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate.CompositeGapAccelerated

lemma curvature_pos (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) : 0 < curvature p Δ := by
  unfold curvature
  positivity

lemma scale_formula (p : Params) (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    scale p Δ = 1 + p.H0 * p.R ^ 2 / Δ + p.H1 * p.R ^ 2 := by
  unfold scale curvature
  field_simp
  ring

lemma scale_ge_one (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) : 1 ≤ scale p Δ := by
  rw [scale_formula p hR hΔ]
  have h₁ : 0 ≤ p.H0 * p.R ^ 2 / Δ := by positivity
  have h₂ : 0 ≤ p.H1 * p.R ^ 2 := by positivity
  linarith

lemma fraction_pos (p : Params) (Δ : ℝ) : 0 < fraction p Δ := by
  unfold fraction
  positivity

lemma fraction_le (p : Params) (Δ : ℝ) : fraction p Δ ≤ 1 / 128 := by
  unfold fraction
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  nlinarith [Real.sqrt_nonneg (scale p Δ)]

lemma fraction_sqrt_scale (p : Params) (Δ : ℝ) :
    fraction p Δ * Real.sqrt (scale p Δ) ≤ 1 / 128 := by
  have hpos : 0 < 128 * (1 + Real.sqrt (scale p Δ)) := by positivity
  unfold fraction
  apply (mul_le_mul_iff_left₀ hpos).mp
  field_simp
  nlinarith [Real.sqrt_nonneg (scale p Δ)]

lemma fraction_geometry (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    fraction p Δ * p.R * Real.sqrt (curvature p Δ * Δ) ≤ Δ / 128 := by
  have hM := curvature_pos p h0 h1 hR hΔ
  have hD := scale_ge_one p h0 h1 hR hΔ
  have hs := fraction_sqrt_scale p Δ
  have hs0 := fraction_pos p Δ
  have hsqD := Real.sq_sqrt (show 0 ≤ scale p Δ by linarith)
  have hsqM := Real.sq_sqrt (show 0 ≤ curvature p Δ * Δ by positivity)
  have hDs : scale p Δ * Δ = curvature p Δ * p.R ^ 2 := by
    unfold scale
    field_simp
  have hsq : (fraction p Δ * Real.sqrt (scale p Δ)) ^ 2 ≤ (1 / 128 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mpr hs
  rw [mul_pow, hsqD] at hsq
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg Δ)
  have he : fraction p Δ ^ 2 * scale p Δ * Δ ^ 2 =
      (fraction p Δ * p.R * Real.sqrt (curvature p Δ * Δ)) ^ 2 := by
    rw [mul_pow, mul_pow, hsqM]
    calc
      _ = fraction p Δ ^ 2 * (scale p Δ * Δ) * Δ := by ring
      _ = _ := by rw [hDs]; ring
  rw [he] at hmul
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith only [hmul]

lemma target_pos (p : Params) (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < target p Δ := by
  unfold target
  positivity

lemma weight_bounds (p : Params) {Δ A : ℝ} (hA : 0 < A)
    (hAt : A < target p Δ) :
    0 < weight p Δ A ∧ A + weight p Δ A ≤ target p Δ ∧
    weight p Δ A ≤ fraction p Δ * (A + weight p Δ A) := by
  have hθ := fraction_pos p Δ
  have hθle := fraction_le p Δ
  have hden : 0 < 1 - fraction p Δ := by linarith
  rw [weight, ite_eq_right hA.ne']
  have hleft : 0 < target p Δ - A := by linarith
  have hright : 0 < A * fraction p Δ / (1 - fraction p Δ) := by positivity
  refine ⟨lt_min hleft hright, ?_, ?_⟩
  · linarith [min_le_left (target p Δ - A) (A * fraction p Δ / (1 - fraction p Δ))]
  · have hh := min_le_right (target p Δ - A) (A * fraction p Δ / (1 - fraction p Δ))
    have he := (le_div_iff₀ hden).mp hh
    nlinarith only [he]

lemma weight_condition (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ A : ℝ} (hΔ : 0 < Δ) (hA : 0 < A)
    (hAt : A < target p Δ) :
    4 * curvature p Δ * (weight p Δ A) ^ 2 ≤ A + weight p Δ A := by
  obtain ⟨ha, hcap, hratio⟩ := weight_bounds p hA hAt
  have hM := curvature_pos p h0 h1 hR hΔ
  have hθ := fraction_pos p Δ
  have hD := scale_ge_one p h0 h1 hR hΔ
  have hs := fraction_sqrt_scale p Δ
  have hs' : fraction p Δ ^ 2 * scale p Δ ≤ (1 / 128 : ℝ) ^ 2 := by
    have hh := (sq_le_sq₀ (show 0 ≤ fraction p Δ * Real.sqrt (scale p Δ) by positivity)
      (show (0 : ℝ) ≤ 1 / 128 by norm_num)).mpr hs
    simpa only [mul_pow, Real.sq_sqrt (show 0 ≤ scale p Δ by linarith)] using hh
  have hat : weight p Δ A ≤ fraction p Δ * target p Δ :=
    hratio.trans (mul_le_mul_of_nonneg_left hcap hθ.le)
  have hp := mul_le_mul hratio hat ha.le (by positivity : 0 ≤ fraction p Δ * (A + weight p Δ A))
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * curvature p Δ by positivity)
  have he : curvature p Δ * target p Δ = scale p Δ := by
    unfold target scale
    ring
  have hre : 4 * curvature p Δ *
      ((fraction p Δ * (A + weight p Δ A)) * (fraction p Δ * target p Δ)) =
      4 * (fraction p Δ ^ 2 * scale p Δ) * (A + weight p Δ A) := by
    rw [← he]
    ring
  rw [hre] at hp'
  have hh := mul_le_mul_of_nonneg_right hs' (show 0 ≤ A + weight p Δ A by positivity)
  nlinarith only [hp', hh, show 0 < A + weight p Δ A by positivity]

lemma fraction_radius (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    fraction p Δ * Real.sqrt p.H1 * p.R ≤ 1 / 128 := by
  have hD := scale_formula p hR hΔ
  have hc : p.H1 * p.R ^ 2 ≤ scale p Δ := by
    rw [hD]
    have hh : 0 ≤ p.H0 * p.R ^ 2 / Δ := by positivity
    linarith
  have hr : Real.sqrt p.H1 * p.R ≤ Real.sqrt (scale p Δ) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt (by linarith [scale_ge_one p h0 h1 hR hΔ])]
    exact hc
  have hh := mul_le_mul_of_nonneg_left hr (fraction_pos p Δ).le
  nlinarith only [hh, fraction_sqrt_scale p Δ]

lemma fraction_quadratic (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    curvature p Δ * p.R ^ 2 * fraction p Δ ^ 2 ≤ Δ / 16384 := by
  have hh := fraction_geometry p h0 h1 hR hΔ
  have hθ := fraction_pos p Δ
  have hM := curvature_pos p h0 h1 hR hΔ
  have hs := (sq_le_sq₀ (show 0 ≤ fraction p Δ * p.R * Real.sqrt (curvature p Δ * Δ)
    by positivity) (show 0 ≤ Δ / 128 by positivity)).mpr hh
  rw [mul_pow, mul_pow, Real.sq_sqrt (show 0 ≤ curvature p Δ * Δ by positivity)] at hs
  apply (mul_le_mul_iff_right₀ hΔ).mp
  nlinarith only [hs]

lemma weight_displacement_bounds (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ A : ℝ} (hΔ : 0 < Δ) (hA : 0 < A)
    (hAt : A < target p Δ) :
    weight p Δ A * (8 * Real.sqrt (curvature p Δ * Δ)) ≤ p.R / 8 ∧
    weight p Δ A * (Δ + 16 * p.R * Real.sqrt (curvature p Δ * Δ)) ≤ p.R ^ 2 / 4 := by
  obtain ⟨ha, hcap, hratio⟩ := weight_bounds p hA hAt
  have hθ := fraction_pos p Δ
  have ht := hratio.trans (mul_le_mul_of_nonneg_left hcap hθ.le)
  have ht' : weight p Δ A * Δ ≤ fraction p Δ * p.R ^ 2 := by
    dsimp [target] at ht
    have hh := mul_le_mul_of_nonneg_right ht hΔ.le
    field_simp at hh
    nlinarith only [hh]
  have hf := fraction_geometry p h0 h1 hR hΔ
  have hlin : weight p Δ A * Real.sqrt (curvature p Δ * Δ) ≤ p.R / 128 := by
    have hh := mul_le_mul_of_nonneg_right ht' (Real.sqrt_nonneg (curvature p Δ * Δ))
    have hr := mul_le_mul_of_nonneg_right hf hR.le
    apply (mul_le_mul_iff_right₀ hΔ).mp
    nlinarith only [hh, hr]
  have hθle := mul_le_mul_of_nonneg_right (fraction_le p Δ) (sq_nonneg p.R)
  have hj := mul_le_mul_of_nonneg_left hlin hR.le
  constructor <;> nlinarith only [hlin, ht', hθle, hj, hR, sq_nonneg p.R]

end LongTails.Proofs.CompositeGapTuning
