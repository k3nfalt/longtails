import LongTails.Proofs.SymmetricReverseFisherScalar
open MeasureTheory ProbabilityTheory
namespace LongTails.Proofs.SymmetricReverseFisherHermite
open LongTails.Proofs.SymmetricReverseFisherGaussian
open LongTails.Proofs.SymmetricReverseFisherRadial
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherHyperbolic
lemma integrable_gaussian_power (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) n (by simp)).integrable_norm_pow'
  refine h.mono' (by fun_prop) ?_
  exact ae_of_all _ (fun x => by simp [Real.norm_eq_abs])
lemma gaussian_fourth_moment : (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 1) = 3 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_id x).pow 3 using 1
    · rfl
    · simp
  have h := gaussian_stein 0 (fun x => x ^ 3) (fun x => 3 * x ^ 2) hd
    (integrable_gaussian_power 3) ((integrable_gaussian_power 2).const_mul 3)
    (by convert integrable_gaussian_power 4 using 1; ext x; ring)
  have he : (∫ x : ℝ, (x - 0) * x ^ 3 ∂gaussianReal 0 1) =
      ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [he, integral_const_mul, gaussian_second_moment] at h
  linarith
lemma gaussian_abs_third_moment : (∫ z : ℝ, |z| ^ 3 ∂gaussianReal 0 1) ≤ 2 := by
  have hi : Integrable (fun z : ℝ => |z| ^ 3) (gaussianReal 0 1) := by
    simpa [abs_pow] using (integrable_gaussian_power 3).abs
  have hpt (z : ℝ) : |z| ^ 3 ≤ (z ^ 2 + z ^ 4) / 2 := by
    have h : 0 ≤ |z| ^ 2 * (|z| - 1) ^ 2 := by positivity
    have h4 : |z| ^ 4 = z ^ 4 := by
      calc
        _ = (|z| ^ 2) ^ 2 := by ring
        _ = _ := by rw [sq_abs]; ring
    nlinarith [sq_abs z]
  have h := integral_mono hi (((integrable_gaussian_power 2).add (integrable_gaussian_power 4)).div_const 2) hpt
  erw [integral_div, integral_add (integrable_gaussian_power 2) (integrable_gaussian_power 4),
    gaussian_second_moment, gaussian_fourth_moment] at h
  norm_num at h ⊢
  exact h
lemma gaussian_stein_weighted (P P' f f' : ℝ → ℝ) {C D : ℝ}
    (hP : Integrable P (gaussianReal 0 1)) (hP' : Integrable P' (gaussianReal 0 1))
    (hxP : Integrable (fun x => x * P x) (gaussianReal 0 1))
    (hdP : ∀ x, HasDerivAt P (P' x) x) (hf' : Continuous f')
    (hdf : ∀ y, HasDerivAt f (f' y) y) (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D)
    (a c : ℝ) :
    a * (∫ x, P x * f' (a * x + c) ∂gaussianReal 0 1) =
      (∫ x, x * P x * f (a * x + c) ∂gaussianReal 0 1) -
        ∫ x, P' x * f (a * x + c) ∂gaussianReal 0 1 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hdf x).continuousAt)
  have hi := integrable_weighted_bounded (gaussianReal 0 1) P f hP hf hC a c
  have hiP := integrable_weighted_bounded (gaussianReal 0 1) P' f hP' hf hC a c
  have hif := integrable_weighted_bounded (gaussianReal 0 1) P f' hP hf' hD a c
  have hix := integrable_weighted_bounded (gaussianReal 0 1) (fun x => x * P x) f hxP hf hC a c
  have hd (x : ℝ) : HasDerivAt (fun y => P y * f (a * y + c))
      (P' x * f (a * x + c) + a * (P x * f' (a * x + c))) x := by
    convert (hdP x).mul ((hdf (a * x + c)).comp x (((hasDerivAt_id x).const_mul a).add_const c)) using 1
    · rfl
    · simp only [Function.comp_apply, id_eq]
      ring
  have h := gaussian_stein 0 _ _ hd hi (hiP.add (hif.const_mul a))
    (by convert hix using 1; ext x; ring)
  erw [integral_add hiP (hif.const_mul a), integral_const_mul] at h
  have he : (∫ x, (x - 0) * (P x * f (a * x + c)) ∂gaussianReal 0 1) =
      ∫ x, x * P x * f (a * x + c) ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [he] at h
  linarith
lemma gaussian_stein_affine (f f' : ℝ → ℝ) {C D : ℝ}
    (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (a c : ℝ) :
    a * (∫ x, f' (a * x + c) ∂gaussianReal 0 1) =
      ∫ x, x * f (a * x + c) ∂gaussianReal 0 1 := by
  have h := gaussian_stein_weighted (fun _ => 1) (fun _ => 0) f f'
    (integrable_const 1) (integrable_const 0)
    (by convert (integrable_gaussian_power 1) using 1; ext x; simp)
    (fun x => hasDerivAt_const x 1) hf' hd hC hD a c
  simpa using h
lemma gaussian_stein_affine_linear (f f' : ℝ → ℝ) {C D : ℝ}
    (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (a c : ℝ) :
    a * (∫ x, x * f' (a * x + c) ∂gaussianReal 0 1) =
      (∫ x, x ^ 2 * f (a * x + c) ∂gaussianReal 0 1) -
        ∫ x, f (a * x + c) ∂gaussianReal 0 1 := by
  have h := gaussian_stein_weighted (fun x => x) (fun _ => 1) f f'
    IsGaussian.integrable_id (integrable_const 1)
    (by convert (integrable_gaussian_power 2) using 1; ext x; ring)
    hasDerivAt_id hf' hd hC hD a c
  simpa [pow_two] using h
lemma gaussian_stein_affine_sq (f f' : ℝ → ℝ) {C D : ℝ}
    (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (a c : ℝ) :
    a * (∫ x, x ^ 2 * f' (a * x + c) ∂gaussianReal 0 1) =
      (∫ x, x ^ 3 * f (a * x + c) ∂gaussianReal 0 1) -
        2 * ∫ x, x * f (a * x + c) ∂gaussianReal 0 1 := by
  have hdP (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    · rfl
    · simp
  have h := gaussian_stein_weighted (fun x => x ^ 2) (fun x => 2 * x) f f'
    (integrable_gaussian_power 2) (IsGaussian.integrable_id.const_mul 2)
    (by convert (integrable_gaussian_power 3) using 1; ext x; ring)
    hdP hf' hd hC hD a c
  have he (x : ℝ) : x * x ^ 2 * f (a * x + c) = x ^ 3 * f (a * x + c) := by ring
  have he' (x : ℝ) : 2 * x * f (a * x + c) = 2 * (x * f (a * x + c)) := by ring
  simp_rw [he, he', integral_const_mul] at h
  exact h
noncomputable def sechSquaredSecond (y : ℝ) : ℝ := 4 * sech y ^ 2 - 6 * sech y ^ 4
lemma hasDerivAt_sech_sq_prime (y : ℝ) :
    HasDerivAt (fun x => -2 * Real.tanh x * sech x ^ 2) (sechSquaredSecond y) y := by
  convert ((hasDerivAt_tanh y).const_mul (-2)).mul (hasDerivAt_sech_sq y) using 1
  unfold sechSquaredSecond
  linear_combination -4 * sech y ^ 2 * tanh_sq_add_sech_sq y
lemma abs_sechSquaredSecond_le_two (y : ℝ) : |sechSquaredSecond y| ≤ 2 := by
  have hs : sech y ^ 2 ≤ 1 := by
    simpa only [abs_of_nonneg (sq_nonneg (sech y))] using abs_sech_sq_le_one y
  unfold sechSquaredSecond
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ 6 * sech y ^ 2 + 2 by positivity),
    sq_nonneg (sech y ^ 2 - 1 / 3)]
lemma gaussian_tanh_hermite (a c : ℝ) :
    a ^ 3 * (∫ z, sechSquaredSecond (a * z + c) ∂gaussianReal 0 1) =
      (∫ z, z ^ 3 * Real.tanh (a * z + c) ∂gaussianReal 0 1) -
        3 * ∫ z, z * Real.tanh (a * z + c) ∂gaussianReal 0 1 := by
  have h0 := gaussian_stein_affine Real.tanh (fun y => sech y ^ 2)
    (by fun_prop) hasDerivAt_tanh (fun y => (Real.abs_tanh_lt_one y).le) abs_sech_sq_le_one a c
  have h1 := gaussian_stein_affine_sq Real.tanh (fun y => sech y ^ 2)
    (by fun_prop) hasDerivAt_tanh (fun y => (Real.abs_tanh_lt_one y).le) abs_sech_sq_le_one a c
  have h2 := gaussian_stein_affine_linear (fun y => sech y ^ 2)
    (fun y => -2 * Real.tanh y * sech y ^ 2) (by fun_prop) hasDerivAt_sech_sq
    abs_sech_sq_le_one abs_sech_sq_derivative_le_two a c
  have h3 := gaussian_stein_affine (fun y => -2 * Real.tanh y * sech y ^ 2) sechSquaredSecond
    (by unfold sechSquaredSecond; fun_prop) hasDerivAt_sech_sq_prime
    abs_sech_sq_derivative_le_two abs_sechSquaredSecond_le_two a c
  linear_combination a ^ 2 * h3 + a * h2 + h1 - h0
lemma gaussian_weighted_tanh_bound (n : ℕ) (a c : ℝ) :
    |∫ z, z ^ n * Real.tanh (a * z + c) ∂gaussianReal 0 1| ≤
      ∫ z, |z| ^ n ∂gaussianReal 0 1 := by
  have hi := integrable_weighted_bounded (gaussianReal 0 1) (fun z => z ^ n) Real.tanh
    (integrable_gaussian_power n) (by fun_prop) (fun y => (Real.abs_tanh_lt_one y).le) a c
  calc
    _ ≤ ∫ z, |z ^ n * Real.tanh (a * z + c)| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono hi.abs (by simpa [abs_pow] using (integrable_gaussian_power n).abs)
      (fun z => by
        rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_tanh_lt_one _).le)
lemma gaussian_tanh_hermite_bound (a c : ℝ) :
    |a ^ 3 * (∫ z, sechSquaredSecond (a * z + c) ∂gaussianReal 0 1)| ≤ 5 := by
  rw [gaussian_tanh_hermite]
  have h3 := (gaussian_weighted_tanh_bound 3 a c).trans gaussian_abs_third_moment
  have h1 : |∫ z, z * Real.tanh (a * z + c) ∂gaussianReal 0 1| ≤ 1 := by
    simpa using (gaussian_weighted_tanh_bound 1 a c).trans (by simpa using gaussian_abs_moment_le)
  have h := abs_sub_le (∫ z, z ^ 3 * Real.tanh (a * z + c) ∂gaussianReal 0 1) 0
    (3 * ∫ z, z * Real.tanh (a * z + c) ∂gaussianReal 0 1)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
  linarith
end LongTails.Proofs.SymmetricReverseFisherHermite
