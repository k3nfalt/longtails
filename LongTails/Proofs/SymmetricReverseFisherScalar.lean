import LongTails.Proofs.SymmetricReverseFisherLoss
import LongTails.Proofs.SymmetricReverseFisherRadial
open MeasureTheory ProbabilityTheory
namespace LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherRadial
open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherGaussian
lemma radialSelf_tilt (r : ℝ) :
    radialSelf r = r ^ 2 - r ^ 2 * Real.exp (-r ^ 2 / 2) *
      ∫ z, sech (r * z) ∂gaussianReal 0 1 := by
  have hi : Integrable (fun x => sech (r * x) ^ 2) (gaussianReal r 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by unfold sech; fun_prop) ?_
    exact ae_of_all _ (fun x => abs_sech_sq_le_one (r * x))
  have he (x : ℝ) : Real.tanh (r * x) ^ 2 = 1 - sech (r * x) ^ 2 := by
    linarith [tanh_sq_add_sech_sq (r * x)]
  unfold radialSelf
  simp_rw [he]
  rw [integral_sub (integrable_const _) hi, gaussian_sech_sq_tilt]
  simp
  ring
noncomputable def sechAverage (r : ℝ) : ℝ := ∫ z, sech (r * z) ∂gaussianReal 0 1
noncomputable def sechAveragePrime (r : ℝ) : ℝ :=
  ∫ z, z * (-Real.tanh (r * z) * sech (r * z)) ∂gaussianReal 0 1
noncomputable def sechAverageSecond (r : ℝ) : ℝ :=
  ∫ z, z ^ 2 * (sech (r * z) * (1 - 2 * sech (r * z) ^ 2)) ∂gaussianReal 0 1

lemma sech_derivative_bound (y : ℝ) : |-Real.tanh y * sech y| ≤ 1 := by
  rw [abs_mul, abs_neg, abs_of_pos (sech_pos y)]
  calc
    _ ≤ 1 * sech y := mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one y).le (sech_pos y).le
    _ ≤ 1 := by simpa using sech_le_one y

lemma hasDerivAt_sech_derivative (y : ℝ) :
    HasDerivAt (fun x => -Real.tanh x * sech x) (sech y * (1 - 2 * sech y ^ 2)) y := by
  convert (hasDerivAt_tanh y).neg.mul (hasDerivAt_sech y) using 1
  simp only [Pi.neg_apply]
  linear_combination -sech y * tanh_sq_add_sech_sq y

lemma sech_second_bound (y : ℝ) : |sech y * (1 - 2 * sech y ^ 2)| ≤ 1 := by
  have hs : sech y ^ 2 ≤ 1 := by nlinarith [sech_pos y, sech_le_one y]
  have hb : |1 - 2 * sech y ^ 2| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith [sq_nonneg (sech y)]⟩
  rw [abs_mul, abs_of_pos (sech_pos y)]
  exact (mul_le_mul_of_nonneg_left hb (sech_pos y).le).trans (by simpa using sech_le_one y)

lemma hasDerivAt_sechAverage (r : ℝ) : HasDerivAt sechAverage (sechAveragePrime r) r := by
  have h := hasDerivAt_weighted_integral (gaussianReal 0 1) (fun _ => 1) sech
    (fun y => -Real.tanh y * sech y) (integrable_const 1)
    (by
      convert (IsGaussian.integrable_id (μ := gaussianReal 0 1)) using 1
      ext x
      simp)
    (by
      have hc : Continuous sech := continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_sech y).continuousAt)
      fun_prop) hasDerivAt_sech
    (fun y => by rw [abs_of_pos (sech_pos y)]; exact sech_le_one y) sech_derivative_bound r 0
  change HasDerivAt (fun t => ∫ z, sech (t * z) ∂gaussianReal 0 1) _ r
  simpa [sechAveragePrime] using h

lemma hasDerivAt_sechAveragePrime (r : ℝ) :
    HasDerivAt sechAveragePrime (sechAverageSecond r) r := by
  have h := hasDerivAt_weighted_integral (gaussianReal 0 1) (fun z => z)
    (fun y => -Real.tanh y * sech y) (fun y => sech y * (1 - 2 * sech y ^ 2))
    IsGaussian.integrable_id
    (by simpa [pow_two] using (IsGaussian.memLp_two_id.integrable_sq (μ := gaussianReal 0 1)))
    (by
      have hc : Continuous sech := continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_sech y).continuousAt)
      fun_prop) hasDerivAt_sech_derivative sech_derivative_bound sech_second_bound r 0
  change HasDerivAt (fun t => ∫ z, z * (-Real.tanh (t * z) * sech (t * z)) ∂gaussianReal 0 1) _ r
  simpa [sechAverageSecond, pow_two] using h

noncomputable def radialFirst (r : ℝ) : ℝ :=
  2 * r - r * (2 - r ^ 2) * Real.exp (-r ^ 2 / 2) * sechAverage r -
    r ^ 2 * Real.exp (-r ^ 2 / 2) * sechAveragePrime r

lemma hasDerivAt_radialSelf (r : ℝ) : HasDerivAt radialSelf (radialFirst r) r := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2 / 2))
      (-r * Real.exp (-r ^ 2 / 2)) r := by
    convert (((hasDerivAt_id r).pow 2).neg.div_const 2).exp using 1 <;> (simp only [Pi.pow_apply, Pi.neg_apply, id_eq]; try ring)
  have h := ((hasDerivAt_id r).pow 2).sub
    ((((hasDerivAt_id r).pow 2).mul he).mul (hasDerivAt_sechAverage r))
  convert h using 1
  · ext t
    exact radialSelf_tilt t
  · simp only [radialFirst, Pi.pow_apply, Pi.mul_apply, id_eq]
    ring
noncomputable def radialSecond (r : ℝ) : ℝ :=
  2 - (2 - 5 * r ^ 2 + r ^ 4) * Real.exp (-r ^ 2 / 2) * sechAverage r -
    2 * r * (2 - r ^ 2) * Real.exp (-r ^ 2 / 2) * sechAveragePrime r -
    r ^ 2 * Real.exp (-r ^ 2 / 2) * sechAverageSecond r

lemma hasDerivAt_radialFirst (r : ℝ) : HasDerivAt radialFirst (radialSecond r) r := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2 / 2))
      (-r * Real.exp (-r ^ 2 / 2)) r := by
    convert (((hasDerivAt_id r).pow 2).neg.div_const 2).exp using 1 <;>
      (simp only [Pi.pow_apply, Pi.neg_apply, id_eq]; try ring)
  have h := ((hasDerivAt_id r).const_mul 2).sub
    (((((hasDerivAt_id r).mul ((hasDerivAt_const r 2).sub ((hasDerivAt_id r).pow 2))).mul he).mul
      (hasDerivAt_sechAverage r)))
  have h' := h.sub ((((hasDerivAt_id r).pow 2).mul he).mul (hasDerivAt_sechAveragePrime r))
  convert h' using 1
  · rfl
  · simp only [radialSecond, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
    ring

lemma gaussian_second_moment : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

lemma gaussian_abs_moment_le : (∫ z : ℝ, |z| ∂gaussianReal 0 1) ≤ 1 := by
  have hi : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) :=
    IsGaussian.memLp_two_id.integrable_sq
  have h := integral_mono (IsGaussian.integrable_id.abs (μ := gaussianReal 0 1))
    (((integrable_const (1 : ℝ)).add hi).div_const 2)
    (fun z => show |z| ≤ (1 + z ^ 2) / 2 by nlinarith [sq_nonneg (|z| - 1), sq_abs z])
  erw [integral_div, integral_add (integrable_const _) hi, gaussian_second_moment] at h
  simpa using h

lemma sechAverage_bound (r : ℝ) : |sechAverage r| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (ae_of_all _ (fun z => show ‖sech (r * z)‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_pos (sech_pos _)]; exact sech_le_one _))
  simpa [sechAverage] using h

lemma sechAveragePrime_bound (r : ℝ) : |sechAveragePrime r| ≤ 1 := by
  have hi : Integrable (fun z => z * (-Real.tanh (r * z) * sech (r * z))) (gaussianReal 0 1) := by
    have hc : Continuous (fun y => -Real.tanh y * sech y) := by
      have hs : Continuous sech := continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_sech y).continuousAt)
      fun_prop
    simpa using integrable_weighted_bounded (gaussianReal 0 1) (fun z => z)
      (fun y => -Real.tanh y * sech y) IsGaussian.integrable_id hc sech_derivative_bound r 0
  calc
    _ ≤ ∫ z, |z * (-Real.tanh (r * z) * sech (r * z))| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, |z| ∂gaussianReal 0 1 := integral_mono hi.abs IsGaussian.integrable_id.abs
      (fun z => by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (sech_derivative_bound _))
    _ ≤ 1 := gaussian_abs_moment_le

lemma sechAverageSecond_bound (r : ℝ) : |sechAverageSecond r| ≤ 1 := by
  have hi : Integrable (fun z => z ^ 2 * (sech (r * z) * (1 - 2 * sech (r * z) ^ 2)))
      (gaussianReal 0 1) := by
    have hc : Continuous (fun y => sech y * (1 - 2 * sech y ^ 2)) := by
      have hs : Continuous sech := continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_sech y).continuousAt)
      fun_prop
    simpa using integrable_weighted_bounded (gaussianReal 0 1) (fun z => z ^ 2)
      (fun y => sech y * (1 - 2 * sech y ^ 2)) IsGaussian.memLp_two_id.integrable_sq hc sech_second_bound r 0
  calc
    _ ≤ ∫ z, |z ^ 2 * (sech (r * z) * (1 - 2 * sech (r * z) ^ 2))| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, z ^ 2 ∂gaussianReal 0 1 := integral_mono hi.abs IsGaussian.memLp_two_id.integrable_sq
      (fun z => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_of_le_one_right (sq_nonneg _) (sech_second_bound _))
    _ = 1 := gaussian_second_moment
noncomputable def ridgeForce (a c : ℝ) : ℝ :=
  2 * (∫ y, Real.tanh y ∂gaussianReal c (a ^ 2).toNNReal) +
    2 * c * (∫ y, sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal) -
    2 * a ^ 2 * (∫ y, Real.tanh y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal)
lemma hasDerivAt_scalarPotential (a c : ℝ) :
    HasDerivAt (scalarPotential a) (-ridgeForce a c) c := by
  have ht := hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal Real.tanh
    (fun y => sech y ^ 2) (by fun_prop) hasDerivAt_tanh
    (fun y => (Real.abs_tanh_lt_one y).le) abs_sech_sq_le_one c
  have hs := hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal (fun y => sech y ^ 2)
    (fun y => -2 * Real.tanh y * sech y ^ 2) (by fun_prop) hasDerivAt_sech_sq
    abs_sech_sq_le_one abs_sech_sq_derivative_le_two c
  have he : (∫ y, -2 * Real.tanh y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal) =
      -2 * ∫ y, Real.tanh y * sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by ring)
  rw [he] at hs
  have h := (((hasDerivAt_const c 1).sub hs).const_mul (a ^ 2)).sub
    (((hasDerivAt_id c).const_mul 2).mul ht)
  convert h using 1
  · rfl
  · simp only [ridgeForce, id_eq]
    ring
lemma sq_mul_exp_bound (r : ℝ) {c : ℝ} (hc : 0 < c) :
    r ^ 2 * Real.exp (-r ^ 2 / c) ≤ c := by
  have he : r ^ 2 / c ≤ Real.exp (r ^ 2 / c) := (Real.add_one_le_exp _).trans' (by linarith)
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-r ^ 2 / c)).le
  have hid : Real.exp (r ^ 2 / c) * Real.exp (-r ^ 2 / c) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at h
  have h' : (r ^ 2 * Real.exp (-r ^ 2 / c)) / c ≤ 1 := by
    convert h using 1
    ring
  simpa using (div_le_iff₀ hc).mp h'
lemma first_mul_exp_bound (r : ℝ) :
    r * Real.exp (-r ^ 2 / 2) ≤ 1 := by
  have he : r ≤ Real.exp (r ^ 2 / 2) := by
    nlinarith [Real.add_one_le_exp (r ^ 2 / 2), sq_nonneg (r - 1)]
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-r ^ 2 / 2)).le
  have hid : Real.exp (r ^ 2 / 2) * Real.exp (-r ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rwa [hid] at h
lemma third_mul_exp_bound {r : ℝ} (hr : 0 ≤ r) :
    r ^ 3 * Real.exp (-r ^ 2 / 2) ≤ 6 := by
  let v := r * Real.exp (-r ^ 2 / 6)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hv2 : v ^ 2 ≤ 3 := by
    have he : v ^ 2 = r ^ 2 * Real.exp (-r ^ 2 / 3) := by
      dsimp [v]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      congr 1
      ring
    rw [he]
    exact sq_mul_exp_bound r (by norm_num)
  have hv1 : v ≤ 2 := by nlinarith
  have hv3 : v ^ 3 ≤ 6 := by nlinarith [mul_le_mul_of_nonneg_right hv2 hv]
  have he : v ^ 3 = r ^ 3 * Real.exp (-r ^ 2 / 2) := by
    dsimp [v]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  rwa [he] at hv3
lemma fourth_mul_exp_bound (r : ℝ) :
    r ^ 4 * Real.exp (-r ^ 2 / 2) ≤ 16 := by
  have h := sq_mul_exp_bound r (c := 4) (by norm_num)
  have hp : 0 ≤ r ^ 2 * Real.exp (-r ^ 2 / 4) := by positivity
  have hs : (r ^ 2 * Real.exp (-r ^ 2 / 4)) ^ 2 ≤ 16 := by nlinarith
  have he : (r ^ 2 * Real.exp (-r ^ 2 / 4)) ^ 2 = r ^ 4 * Real.exp (-r ^ 2 / 2) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    · ring
    · congr 1
      ring
  rwa [he] at hs
lemma radialSecond_bound_nonneg {r : ℝ} (hr : 0 ≤ r) : |radialSecond r| ≤ 48 := by
  let e := Real.exp (-r ^ 2 / 2)
  have he : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  have h1 : r * e ≤ 1 := first_mul_exp_bound r
  have h2 : r ^ 2 * e ≤ 2 := sq_mul_exp_bound r (by norm_num)
  have h3 : r ^ 3 * e ≤ 6 := third_mul_exp_bound hr
  have h4 : r ^ 4 * e ≤ 16 := fourth_mul_exp_bound r
  have hc : |2 - 5 * r ^ 2 + r ^ 4| ≤ 2 + 5 * r ^ 2 + r ^ 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  have ha : |(2 - 5 * r ^ 2 + r ^ 4) * e * sechAverage r| ≤
      (2 + 5 * r ^ 2 + r ^ 4) * e := by
    rw [abs_mul, abs_mul, abs_of_nonneg he]
    calc
      _ ≤ |2 - 5 * r ^ 2 + r ^ 4| * e * 1 :=
        mul_le_mul_of_nonneg_left (sechAverage_bound r) (by positivity)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hc he
  have hd : |2 - r ^ 2| ≤ 2 + r ^ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r]⟩
  have hb : |2 * r * (2 - r ^ 2) * e * sechAveragePrime r| ≤ (4 * r + 2 * r ^ 3) * e := by
    rw [abs_mul]
    calc
      _ ≤ |2 * r * (2 - r ^ 2) * e| * 1 :=
        mul_le_mul_of_nonneg_left (sechAveragePrime_bound r) (abs_nonneg _)
      _ = 2 * r * e * |2 - r ^ 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg he, abs_of_nonneg (by positivity : 0 ≤ 2 * r)]
        ring
      _ ≤ 2 * r * e * (2 + r ^ 2) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  have hc' : |r ^ 2 * e * sechAverageSecond r| ≤ r ^ 2 * e := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 * e)]
    exact mul_le_of_le_one_right (by positivity) (sechAverageSecond_bound r)
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc'' := abs_le.mp hc'
  unfold radialSecond
  change |2 - (2 - 5 * r ^ 2 + r ^ 4) * e * sechAverage r -
    2 * r * (2 - r ^ 2) * e * sechAveragePrime r - r ^ 2 * e * sechAverageSecond r| ≤ 48
  apply abs_le.mpr
  constructor <;> nlinarith
lemma integrable_tanh_scaled (r a : ℝ) :
    Integrable (fun x => Real.tanh (a * x)) (gaussianReal r 1) := by
  simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1) Real.tanh
    (integrable_const 1) (by fun_prop) (fun y => (Real.abs_tanh_lt_one y).le) a 0
lemma integrable_tanh_sq_scaled (r a : ℝ) :
    Integrable (fun x => Real.tanh (a * x) ^ 2) (gaussianReal r 1) := by
  simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1) (fun y => Real.tanh y ^ 2)
    (integrable_const 1) (by fun_prop) (fun y => show |Real.tanh y ^ 2| ≤ 1 by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one y).le) a 0
lemma radialSelf_posterior (r : ℝ) :
    radialSelf r = r ^ 2 * ∫ x, Real.tanh (r * x) ∂gaussianReal r 1 := by
  have h := gaussian_posterior_odd r (fun x => Real.tanh (r * x))
    (fun x => by rw [mul_neg, Real.tanh_neg]) (integrable_tanh_scaled r r)
    (by simpa [pow_two] using integrable_tanh_sq_scaled r r)
  unfold radialSelf
  rw [show (∫ x, Real.tanh (r * x) ^ 2 ∂gaussianReal r 1) =
    ∫ x, Real.tanh (r * x) ∂gaussianReal r 1 by simpa [pow_two] using h]
lemma radialSelf_quadratic (r : ℝ) :
    radialSelf r = r ^ 2 * ∫ z, Real.tanh (r * z + r ^ 2) ∂gaussianReal 0 1 := by
  rw [radialSelf_posterior, gaussian_integral_shift r _ (by fun_prop)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by dsimp only; congr 1; ring)
lemma hasDerivAt_radialSelf_force (r : ℝ) : HasDerivAt radialSelf (radialForce r r) r := by
  have ht := hasDerivAt_quadratic_integral Real.tanh (fun y => sech y ^ 2)
    (by fun_prop) hasDerivAt_tanh (fun y => (Real.abs_tanh_lt_one y).le) abs_sech_sq_le_one r
  have h := ((hasDerivAt_id r).pow 2).mul ht
  convert h using 1
  · ext t
    exact radialSelf_quadratic t
  · rw [radialForce, gaussian_integral_shift r (fun x => Real.tanh (r * x)) (by fun_prop),
      gaussian_integral_shift r (fun x => (x + r) * sech (r * x) ^ 2) (by fun_prop)]
    have ht' : (∫ z, Real.tanh (r * (z + r)) ∂gaussianReal 0 1) =
        ∫ z, Real.tanh (r * z + r ^ 2) ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by dsimp only; congr 1; ring)
    have hs : (∫ z, (z + r + r) * sech (r * (z + r)) ^ 2 ∂gaussianReal 0 1) =
        ∫ z, (z + 2 * r) * sech (r * z + r ^ 2) ^ 2 ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        dsimp only
        rw [show r * (z + r) = r * z + r ^ 2 by ring]
        ring)
    rw [ht', hs]
    simp only [Pi.pow_apply, id_eq]
    ring
lemma radialFirst_eq_force (r : ℝ) : radialFirst r = radialForce r r :=
  (hasDerivAt_radialSelf r).unique (hasDerivAt_radialSelf_force r)
lemma integrable_sech_sq_scaled (r a : ℝ) :
    Integrable (fun x => sech (a * x) ^ 2) (gaussianReal r 1) := by
  simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1) (fun y => sech y ^ 2)
    (integrable_const 1) (by fun_prop) abs_sech_sq_le_one a 0
lemma integrable_tanh_sech_sq_scaled (r a : ℝ) :
    Integrable (fun x => Real.tanh (a * x) * sech (a * x) ^ 2) (gaussianReal r 1) := by
  simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1)
    (fun y => Real.tanh y * sech y ^ 2) (integrable_const 1) (by fun_prop)
    abs_tanh_sech_sq_le_one a 0
lemma integrable_linear_sech_sq (r a b : ℝ) :
    Integrable (fun x => (x + b) * sech (a * x) ^ 2) (gaussianReal r 1) := by
  simpa using integrable_weighted_bounded (gaussianReal r 1) (fun x => x + b)
    (fun y => sech y ^ 2) (IsGaussian.integrable_id.add (integrable_const b))
    (by fun_prop) abs_sech_sq_le_one a 0
lemma gaussian_sech_stein (r a : ℝ) :
    (∫ x, (x - r) * sech (a * x) ^ 2 ∂gaussianReal r 1) =
      -2 * a * ∫ x, Real.tanh (a * x) * sech (a * x) ^ 2 ∂gaussianReal r 1 := by
  have hd (x : ℝ) : HasDerivAt (fun y => sech (a * y) ^ 2)
      (-2 * a * (Real.tanh (a * x) * sech (a * x) ^ 2)) x := by
    convert (hasDerivAt_sech_sq (a * x)).comp x ((hasDerivAt_id x).const_mul a) using 1
    · rfl
    · ring
  have h := gaussian_stein r (fun x => sech (a * x) ^ 2)
    (fun x => -2 * a * (Real.tanh (a * x) * sech (a * x) ^ 2)) hd
    (integrable_sech_sq_scaled r a) ((integrable_tanh_sech_sq_scaled r a).const_mul (-2 * a))
    (by simpa [sub_eq_add_neg] using integrable_linear_sech_sq r a (-r))
  rw [integral_const_mul] at h
  exact h.symm
lemma radialForce_eq_ridgeForce (a r : ℝ) :
    radialForce a r = a * ridgeForce a (a * r) := by
  have hs := gaussian_sech_stein r a
  have he : (∫ x, (x + r) * sech (a * x) ^ 2 ∂gaussianReal r 1) =
      (∫ x, (x - r) * sech (a * x) ^ 2 ∂gaussianReal r 1) +
      2 * r * ∫ x, sech (a * x) ^ 2 ∂gaussianReal r 1 := by
    rw [← integral_const_mul, ← integral_add
      (by simpa [sub_eq_add_neg] using integrable_linear_sech_sq r a (-r))
      ((integrable_sech_sq_scaled r a).const_mul (2 * r))]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp only; ring)
  unfold radialForce ridgeForce
  rw [gaussian_integral_scale r a Real.tanh (by fun_prop),
    gaussian_integral_scale r a (fun y => sech y ^ 2) (by fun_prop),
    gaussian_integral_scale r a (fun y => Real.tanh y * sech y ^ 2) (by fun_prop), he, hs]
  ring
lemma abs_tanh_sq_sech_sq_le_one (y : ℝ) : |Real.tanh y ^ 2 * sech y ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have ht := (sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one y).le
  have hs : sech y ^ 2 ≤ 1 := by simpa only [abs_of_nonneg (sq_nonneg (sech y))] using abs_sech_sq_le_one y
  calc
    _ ≤ 1 * sech y ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    _ ≤ 1 := by simpa using hs
lemma integrable_sech_four_scaled (r a : ℝ) :
    Integrable (fun x => sech (a * x) ^ 4) (gaussianReal r 1) := by
  simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1) (fun y => sech y ^ 4)
    (integrable_const 1) (by fun_prop) (fun y => show |sech y ^ 4| ≤ 1 by
      rw [abs_of_nonneg (by positivity)]
      exact (pow_le_pow_left₀ (sech_pos y).le (sech_le_one y) 4).trans_eq (by norm_num)) a 0
lemma gaussian_tanh_sech_posterior (r : ℝ) :
    (∫ x, Real.tanh (r * x) * sech (r * x) ^ 2 ∂gaussianReal r 1) =
      (∫ x, sech (r * x) ^ 2 ∂gaussianReal r 1) -
      ∫ x, sech (r * x) ^ 4 ∂gaussianReal r 1 := by
  have hi : Integrable (fun x => Real.tanh (r * x) ^ 2 * sech (r * x) ^ 2) (gaussianReal r 1) := by
    simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1)
      (fun y => Real.tanh y ^ 2 * sech y ^ 2) (integrable_const 1) (by fun_prop)
      abs_tanh_sq_sech_sq_le_one r 0
  have hp := gaussian_posterior_odd r (fun x => Real.tanh (r * x) * sech (r * x) ^ 2)
    (fun x => by simp [mul_neg, Real.tanh_neg, sech_neg]) (integrable_tanh_sech_sq_scaled r r)
    (by convert hi using 1; ext x; ring)
  rw [← hp, ← integral_sub (integrable_sech_sq_scaled r r) (integrable_sech_four_scaled r r)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    linear_combination sech (r * x) ^ 2 * tanh_sq_add_sech_sq (r * x))
noncomputable def alpha (r : ℝ) : ℝ :=
  2 * (∫ x, Real.tanh (r * x) ∂gaussianReal r 1) +
    2 * r ^ 2 * ∫ x, sech (r * x) ^ 4 ∂gaussianReal r 1
lemma radialFirst_eq_alpha (r : ℝ) : radialFirst r = r * alpha r := by
  rw [radialFirst_eq_force, radialForce_eq_ridgeForce]
  unfold ridgeForce alpha
  rw [gaussian_integral_scale r r Real.tanh (by fun_prop),
    gaussian_integral_scale r r (fun y => sech y ^ 2) (by fun_prop),
    gaussian_integral_scale r r (fun y => Real.tanh y * sech y ^ 2) (by fun_prop),
    gaussian_tanh_sech_posterior]
  ring
lemma alpha_zero : alpha 0 = 0 := by simp [alpha]
noncomputable def alignedForce (a r : ℝ) : ℝ := radialForce r r - radialForce a r
lemma hasDerivAt_alignedLoss (a r : ℝ) :
    HasDerivAt (fun t => radialSelf t + scalarPotential a (a * t)) (alignedForce a r) r := by
  have h := (hasDerivAt_radialSelf_force r).add
    ((hasDerivAt_scalarPotential a (a * r)).comp r ((hasDerivAt_id r).const_mul a))
  convert h using 1
  · rfl
  · rw [alignedForce, radialForce_eq_ridgeForce a r]
    ring
lemma alignedForce_coercive {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    min r 1 * min (r + a) 1 / 120 * (r - a) ^ 2 ≤ (r - a) * alignedForce a r := by
  unfold alignedForce
  rcases le_total a r with har | hra
  · have h := radialForce_increment_lower ha har hr
    have hm := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr har)
    nlinarith
  · have h := radialForce_increment_lower hr.le hra hr
    rw [add_comm a r] at h
    have hm := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hra)
    nlinarith
lemma alignedForce_self (a : ℝ) : alignedForce a a = 0 := by simp [alignedForce]
end LongTails.Proofs.SymmetricReverseFisherScalar
