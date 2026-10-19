import LongTails.Proofs.SymmetricReverseFisherCoefficients
import LongTails.Proofs.SymmetricReverseFisherHermite
open MeasureTheory ProbabilityTheory
namespace LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherRadial
open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherGaussian
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherHermite
lemma mul_sech_sq_le_one {y : ℝ} (hy : 0 ≤ y) : y * sech y ^ 2 ≤ 1 := by
  rcases hy.eq_or_lt with hy | hy
  · simp [← hy]
  · exact (mul_sech_sq_lt_tanh hy).le.trans ((le_abs_self _).trans (Real.abs_tanh_lt_one y).le)
lemma abs_mul_sech_sq_le_one (y : ℝ) : |y * sech y ^ 2| ≤ 1 := by
  have hs : sech |y| = sech y := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy, sech_neg]
  rw [abs_mul, abs_of_nonneg (sq_nonneg (sech y)), ← hs]
  exact mul_sech_sq_le_one (abs_nonneg y)
lemma integrable_mul_sech_sq (a c : ℝ) :
    Integrable (fun y => y * sech y ^ 2) (gaussianReal c (a ^ 2).toNNReal) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all _ (fun y => abs_mul_sech_sq_le_one y)
lemma ridgeForce_representation (a c : ℝ) :
    ridgeForce a c = 2 * tanhMean a c + c * sechMean a c +
      ∫ y, y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal := by
  by_cases ha : a = 0
  · subst a
    simp [ridgeForce, tanhMean, sechMean]
    ring
  let r := c / a
  have har : a * r = c := by dsimp [r]; field_simp
  have hs := gaussian_sech_stein r a
  have he : (∫ x, (x - r) * sech (a * x) ^ 2 ∂gaussianReal r 1) =
      (∫ x, x * sech (a * x) ^ 2 ∂gaussianReal r 1) -
      r * ∫ x, sech (a * x) ^ 2 ∂gaussianReal r 1 := by
    rw [← integral_const_mul, ← integral_sub
      (by simpa using integrable_linear_sech_sq r a 0) ((integrable_sech_sq_scaled r a).const_mul r)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp only; ring)
  rw [he] at hs
  unfold ridgeForce tanhMean sechMean
  rw [← har]
  rw [gaussian_integral_scale r a Real.tanh (by fun_prop),
    gaussian_integral_scale r a (fun y => sech y ^ 2) (by fun_prop),
    gaussian_integral_scale r a (fun y => Real.tanh y * sech y ^ 2) (by fun_prop),
    gaussian_integral_scale r a (fun y => y * sech y ^ 2) (by fun_prop)]
  have hi : (∫ x, a * x * sech (a * x) ^ 2 ∂gaussianReal r 1) =
      a * ∫ x, x * sech (a * x) ^ 2 ∂gaussianReal r 1 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [hi]
  linear_combination -a * hs
lemma gaussian_mul_sech_sq_nonneg {a c : ℝ} (hc : 0 ≤ c) :
    0 ≤ ∫ y, y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal := by
  have h := gaussian_odd_integral_mono hc (a ^ 2).toNNReal (fun _ => 0)
    (fun y => y * sech y ^ 2) (integrable_const 0)
    (integrable_mul_sech_sq a c) (fun _ => by simp)
    (fun y => by rw [sech_neg]; ring) (fun y hy => by positivity)
  simpa using h
lemma gaussian_mul_sech_sq_le_mean {a c : ℝ} (hc : 0 ≤ c) :
    (∫ y, y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal) ≤ c := by
  have h := gaussian_odd_integral_mono hc (a ^ 2).toNNReal (fun y => y * sech y ^ 2)
    (fun y => y) (integrable_mul_sech_sq a c) IsGaussian.integrable_id
    (fun y => by rw [sech_neg]; ring) (fun _ => rfl)
    (fun y hy => mul_le_of_le_one_right hy.le (by
      simpa only [abs_of_nonneg (sq_nonneg (sech y))] using abs_sech_sq_le_one y))
  simpa using h
lemma ridgeForce_lower {a c : ℝ} (hc : 0 ≤ c) : 2 * tanhMean a c ≤ ridgeForce a c := by
  rw [ridgeForce_representation]
  nlinarith [gaussian_mul_sech_sq_nonneg (a := a) hc, mul_nonneg hc (sechMean_nonneg a c)]
lemma ridgeForce_nonneg {a c : ℝ} (hc : 0 ≤ c) : 0 ≤ ridgeForce a c :=
  (mul_nonneg (by norm_num) (tanhMean_nonneg hc)).trans (ridgeForce_lower hc)
lemma ridgeForce_le_four_mul {a c : ℝ} (hc : 0 ≤ c) : ridgeForce a c ≤ 4 * c := by
  rw [ridgeForce_representation]
  have hT := tanhMean_le_argument (a := a) hc
  have hA := mul_le_mul_of_nonneg_left (sechMean_le_one a c) hc
  have hY := gaussian_mul_sech_sq_le_mean (a := a) hc
  nlinarith
lemma ridgeForce_zero (a : ℝ) : ridgeForce a 0 = 0 := by
  have h0 := ridgeForce_nonneg (a := a) (c := 0) (by norm_num)
  have h1 := ridgeForce_le_four_mul (a := a) (c := 0) (by norm_num)
  linarith
lemma gaussian_reflect_integral (m : ℝ) (v : NNReal) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂gaussianReal (-m) v) = ∫ y, f (-y) ∂gaussianReal m v := by
  rw [← gaussianReal_map_neg, integral_map (by fun_prop) hf.aestronglyMeasurable]
lemma ridgeForce_neg (a c : ℝ) : ridgeForce a (-c) = -ridgeForce a c := by
  unfold ridgeForce
  rw [gaussian_reflect_integral c (a ^ 2).toNNReal Real.tanh (by fun_prop),
    gaussian_reflect_integral c (a ^ 2).toNNReal (fun y => sech y ^ 2) (by fun_prop),
    gaussian_reflect_integral c (a ^ 2).toNNReal (fun y => Real.tanh y * sech y ^ 2) (by fun_prop)]
  simp only [Real.tanh_neg, sech_neg, neg_mul, integral_neg]
  ring
noncomputable def sechMeanPrime (a c : ℝ) : ℝ :=
  -2 * ∫ y, Real.tanh y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal
lemma hasDerivAt_sechMean (a c : ℝ) : HasDerivAt (sechMean a) (sechMeanPrime a c) c := by
  have h := hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal (fun y => sech y ^ 2)
    (fun y => -2 * Real.tanh y * sech y ^ 2) (by fun_prop) hasDerivAt_sech_sq
    abs_sech_sq_le_one abs_sech_sq_derivative_le_two c
  convert h using 1
  · rfl
  · unfold sechMeanPrime
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by ring)
lemma sechMeanPrime_nonpos {a c : ℝ} (hc : 0 ≤ c) : sechMeanPrime a c ≤ 0 := by
  have hi : Integrable (fun y => Real.tanh y * sech y ^ 2) (gaussianReal c (a ^ 2).toNNReal) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ abs_tanh_sech_sq_le_one
  have h := gaussian_odd_integral_mono hc (a ^ 2).toNNReal (fun _ => 0)
    (fun y => Real.tanh y * sech y ^ 2) (integrable_const 0) hi (fun _ => by simp)
    (fun y => by rw [Real.tanh_neg, sech_neg]; ring)
    (fun y hy => mul_nonneg (by
      have h := tanh_monotone hy.le
      simpa using h) (sq_nonneg _))
  simp only [integral_zero] at h
  unfold sechMeanPrime
  linarith
lemma mul_sechMean_le_tanhMean {a c : ℝ} (hc : 0 ≤ c) : c * sechMean a c ≤ tanhMean a c := by
  let F := fun t => tanhMean a t - t * sechMean a t
  have hd (t : ℝ) : HasDerivAt F (-t * sechMeanPrime a t) t := by
    convert (hasDerivAt_tanhMean a t).sub ((hasDerivAt_id t).mul (hasDerivAt_sechMean a t)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht : t ∈ Set.Ici (0 : ℝ))
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ht0) (sechMeanPrime_nonpos ht0)
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hc hc
  dsimp only [F] at h
  rw [tanhMean_zero] at h
  nlinarith
lemma ridgeForce_le_four {a c : ℝ} (hc : 0 ≤ c) : ridgeForce a c ≤ 4 := by
  have hY : (∫ y, y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal) ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := gaussianReal c (a ^ 2).toNNReal)
      (ae_of_all _ (fun y => show ‖y * sech y ^ 2‖ ≤ 1 from abs_mul_sech_sq_le_one y))
    have h' : |∫ y, y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal| ≤ 1 := by simpa using h
    exact (le_abs_self _).trans h'
  rw [ridgeForce_representation]
  have hT := tanhMean_le_one a c
  have hA := mul_sechMean_le_tanhMean (a := a) hc
  linarith
noncomputable def beta (a c : ℝ) : ℝ :=
  if c = 0 then 1 / (150 * (1 + |a|)) else ridgeForce a c / c
lemma beta_mul (a c : ℝ) : beta a c * c = ridgeForce a c := by
  by_cases hc : c = 0
  · simp [hc, ridgeForce_zero]
  · simp [beta, hc]
lemma beta_neg (a c : ℝ) : beta a (-c) = beta a c := by
  by_cases hc : c = 0
  · simp [hc]
  · simp [beta, hc, ridgeForce_neg]
lemma beta_nonneg_nonneg {a c : ℝ} (hc : 0 ≤ c) : 0 ≤ beta a c := by
  by_cases hc0 : c = 0
  · rw [beta, ite_eq_left hc0]
    positivity
  · rw [beta, ite_eq_right hc0]
    exact div_nonneg (ridgeForce_nonneg hc) hc
lemma beta_le_four_nonneg {a c : ℝ} (hc : 0 ≤ c) : beta a c ≤ 4 := by
  by_cases hc0 : c = 0
  · rw [beta, ite_eq_left hc0]
    apply (div_le_iff₀ (by positivity : 0 < 150 * (1 + |a|))).mpr
    nlinarith [abs_nonneg a]
  · rw [beta, ite_eq_right hc0]
    exact (div_le_iff₀ (lt_of_le_of_ne hc (Ne.symm hc0))).mpr (ridgeForce_le_four_mul hc)
lemma beta_nonneg (a c : ℝ) : 0 ≤ beta a c := by
  rcases le_total 0 c with hc | hc
  · exact beta_nonneg_nonneg hc
  · rw [← beta_neg]
    exact beta_nonneg_nonneg (neg_nonneg.mpr hc)
lemma beta_le_four (a c : ℝ) : beta a c ≤ 4 := by
  rcases le_total 0 c with hc | hc
  · exact beta_le_four_nonneg hc
  · rw [← beta_neg]
    exact beta_le_four_nonneg (neg_nonneg.mpr hc)
lemma beta_lower {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    1 / (150 * (1 + a + c)) ≤ beta a c := by
  by_cases hc0 : c = 0
  · simp [beta, hc0, abs_of_nonneg ha]
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hM : 0 < max a 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right a 1)
  have hMa : max a 1 ≤ 1 + a := max_le (by linarith) (by linarith)
  have ht := tanhMean_lower ha hc
  have hb := ridgeForce_lower (a := a) hc
  have hb0 := ridgeForce_nonneg (a := a) hc
  have hb' : min c (max a 1) / (4 * max a 1) ≤ ridgeForce a c := by
    rw [show min c (max a 1) / (4 * max a 1) = 2 * (min c (max a 1) / (8 * max a 1)) by ring]
    linarith
  rw [beta, ite_eq_right hc0]
  apply (div_le_div_iff₀ (by positivity : 0 < 150 * (1 + a + c)) hcpos).mpr
  rcases le_total c (max a 1) with hcm | hmc
  · rw [min_eq_left hcm] at hb'
    have h := (div_le_iff₀ (by positivity : 0 < 4 * max a 1)).mp hb'
    have hscale : 4 * max a 1 ≤ 150 * (1 + a + c) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hscale hb0
    nlinarith
  · rw [min_eq_right hmc] at hb'
    have he : max a 1 / (4 * max a 1) = 1 / 4 := by field_simp
    rw [he] at hb'
    have hscale : 4 * c ≤ 150 * (1 + a + c) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hb' (show 0 ≤ 150 * (1 + a + c) by positivity)
    nlinarith
noncomputable def weightedSechMean (a c : ℝ) : ℝ :=
  ∫ y, y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal
noncomputable def weightedSechPrime (a c : ℝ) : ℝ :=
  ∫ y, sech y ^ 2 - 2 * y * Real.tanh y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal
noncomputable def sechMeanSecond (a c : ℝ) : ℝ :=
  ∫ y, sechSquaredSecond y ∂gaussianReal c (a ^ 2).toNNReal
noncomputable def ridgeDerivative (a c : ℝ) : ℝ :=
  2 * sechMean a c + 2 * weightedSechPrime a c - a ^ 2 * sechMeanSecond a c
lemma hasDerivAt_mul_sech_sq (y : ℝ) :
    HasDerivAt (fun x => x * sech x ^ 2) (sech y ^ 2 - 2 * y * Real.tanh y * sech y ^ 2) y := by
  convert (hasDerivAt_id y).mul (hasDerivAt_sech_sq y) using 1
  · rfl
  · simp only [id_eq]
    ring
lemma abs_mul_sech_sq_prime_le_three (y : ℝ) :
    |sech y ^ 2 - 2 * y * Real.tanh y * sech y ^ 2| ≤ 3 := by
  have h : |2 * y * Real.tanh y * sech y ^ 2| ≤ 2 := by
    have he : 2 * y * Real.tanh y * sech y ^ 2 = 2 * (y * sech y ^ 2) * Real.tanh y := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h0 := abs_mul_sech_sq_le_one y
    have h1 := (Real.abs_tanh_lt_one y).le
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * |y * sech y ^ 2| by positivity)]
  have hs := abs_sech_sq_le_one y
  have ht := abs_sub_le (sech y ^ 2) 0 (2 * y * Real.tanh y * sech y ^ 2)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  linarith
lemma hasDerivAt_weightedSechMean (a c : ℝ) :
    HasDerivAt (weightedSechMean a) (weightedSechPrime a c) c :=
  hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal (fun y => y * sech y ^ 2)
    (fun y => sech y ^ 2 - 2 * y * Real.tanh y * sech y ^ 2) (by fun_prop)
    hasDerivAt_mul_sech_sq abs_mul_sech_sq_le_one abs_mul_sech_sq_prime_le_three c
lemma hasDerivAt_sechMeanPrime (a c : ℝ) :
    HasDerivAt (sechMeanPrime a) (sechMeanSecond a c) c := by
  have h := hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal
    (fun y => -2 * Real.tanh y * sech y ^ 2) sechSquaredSecond
    (by unfold sechSquaredSecond; fun_prop) hasDerivAt_sech_sq_prime
    abs_sech_sq_derivative_le_two abs_sechSquaredSecond_le_two c
  convert h using 1
  · ext t
    unfold sechMeanPrime
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by ring)
  · rfl
lemma ridgeForce_alternate (a c : ℝ) :
    ridgeForce a c = 2 * tanhMean a c + 2 * weightedSechMean a c - a ^ 2 * sechMeanPrime a c := by
  have hr := ridgeForce_representation a c
  change ridgeForce a c = 2 * tanhMean a c + c * sechMean a c + weightedSechMean a c at hr
  have hd : ridgeForce a c = a ^ 2 * sechMeanPrime a c + 2 * tanhMean a c + 2 * c * sechMean a c := by
    unfold ridgeForce sechMeanPrime tanhMean sechMean
    ring
  linarith
lemma hasDerivAt_ridgeForce (a c : ℝ) : HasDerivAt (ridgeForce a) (ridgeDerivative a c) c := by
  have h := (((hasDerivAt_tanhMean a c).const_mul 2).add
    ((hasDerivAt_weightedSechMean a c).const_mul 2)).sub ((hasDerivAt_sechMeanPrime a c).const_mul (a ^ 2))
  convert h using 1
  · ext t
    exact ridgeForce_alternate a t
  · rfl
lemma abs_mul_sechMean_le_one (a c : ℝ) : |a * sechMean a c| ≤ 1 := by
  have h := gaussian_stein_affine Real.tanh (fun y => sech y ^ 2)
    (by fun_prop) hasDerivAt_tanh (fun y => (Real.abs_tanh_lt_one y).le) abs_sech_sq_le_one a c
  have he : sechMean a c = ∫ z, sech (a * z + c) ^ 2 ∂gaussianReal 0 1 :=
    gaussian_affine_integral a c _ (by fun_prop)
  rw [he, h]
  simpa using (gaussian_weighted_tanh_bound 1 a c).trans (by simpa using gaussian_abs_moment_le)
lemma abs_mul_weightedSechPrime_le_one (a c : ℝ) : |a * weightedSechPrime a c| ≤ 1 := by
  have h := gaussian_stein_affine (fun y => y * sech y ^ 2)
    (fun y => sech y ^ 2 - 2 * y * Real.tanh y * sech y ^ 2) (by fun_prop)
    hasDerivAt_mul_sech_sq abs_mul_sech_sq_le_one abs_mul_sech_sq_prime_le_three a c
  have he : weightedSechPrime a c =
      ∫ z, sech (a * z + c) ^ 2 - 2 * (a * z + c) * Real.tanh (a * z + c) * sech (a * z + c) ^ 2
        ∂gaussianReal 0 1 := gaussian_affine_integral a c _ (by fun_prop)
  rw [he, h]
  have hi := integrable_weighted_bounded (gaussianReal 0 1) (fun z => z) (fun y => y * sech y ^ 2)
    IsGaussian.integrable_id (by fun_prop) abs_mul_sech_sq_le_one a c
  calc
    _ ≤ ∫ z, |z * ((a * z + c) * sech (a * z + c) ^ 2)| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ ∫ z, |z| ∂gaussianReal 0 1 := integral_mono hi.abs IsGaussian.integrable_id.abs
      (fun z => by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_mul_sech_sq_le_one _))
    _ ≤ 1 := gaussian_abs_moment_le
lemma abs_cube_mul_sechMeanSecond_le_five (a c : ℝ) : |a ^ 3 * sechMeanSecond a c| ≤ 5 := by
  unfold sechMeanSecond
  rw [gaussian_affine_integral a c sechSquaredSecond (by unfold sechSquaredSecond; fun_prop)]
  exact gaussian_tanh_hermite_bound a c
lemma ridgeDerivative_bound {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    a ^ 2 * |ridgeDerivative a c| ≤ 9 * a := by
  have hA : a * |sechMean a c| ≤ 1 := by
    simpa only [abs_mul, abs_of_nonneg ha] using abs_mul_sechMean_le_one a c
  have hH : a * |weightedSechPrime a c| ≤ 1 := by
    simpa only [abs_mul, abs_of_nonneg ha] using abs_mul_weightedSechPrime_le_one a c
  have hS : a ^ 3 * |sechMeanSecond a c| ≤ 5 := by
    simpa only [abs_mul, abs_of_nonneg (pow_nonneg ha 3)] using abs_cube_mul_sechMeanSecond_le_five a c
  have ht : |ridgeDerivative a c| ≤ 2 * |sechMean a c| + 2 * |weightedSechPrime a c| +
      a ^ 2 * |sechMeanSecond a c| := by
    unfold ridgeDerivative
    have h1 := abs_add_le (2 * sechMean a c) (2 * weightedSechPrime a c)
    have h2 := abs_sub_le (2 * sechMean a c + 2 * weightedSechPrime a c) 0 (a ^ 2 * sechMeanSecond a c)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg a)] at h1 h2
    linarith
  have h := mul_le_mul_of_nonneg_left ht (sq_nonneg a)
  nlinarith [mul_le_mul_of_nonneg_left hA ha, mul_le_mul_of_nonneg_left hH ha,
    mul_le_mul_of_nonneg_left hS ha]
end LongTails.Proofs.SymmetricReverseFisherRidge
