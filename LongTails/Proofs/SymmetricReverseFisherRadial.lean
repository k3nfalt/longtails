import LongTails.Proofs.SymmetricReverseFisherTails
import Mathlib.Analysis.Calculus.ParametricIntegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherGaussian
open LongTails.Proofs.SymmetricReverseFisherKernel
namespace LongTails.Proofs.SymmetricReverseFisherRadial

lemma integrable_weighted_bounded (μ : Measure ℝ) (P f : ℝ → ℝ) {C : ℝ}
    (hP : Integrable P μ) (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) (a b : ℝ) :
    Integrable (fun x => P x * f (a * x + b)) μ := by
  refine (hP.abs.const_mul C).mono'
    (hP.aestronglyMeasurable.mul (hf.comp (by fun_prop)).aestronglyMeasurable) ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hbound (a * x + b)) (abs_nonneg (P x))])

lemma hasDerivAt_weighted_integral (μ : Measure ℝ) (P f f' : ℝ → ℝ) {C D : ℝ}
    (hP : Integrable P μ) (hPx : Integrable (fun x => P x * x) μ)
    (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (a b : ℝ) :
    HasDerivAt (fun t => ∫ x, P x * f (t * x + b) ∂μ)
      (∫ x, P x * x * f' (a * x + b) ∂μ) a := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => P x * f (t * x + b))
    (F' := fun t x => P x * x * f' (t * x + b))
    (bound := fun x => D * |P x * x|) (s := univ) (by simp)
    ?_ (integrable_weighted_bounded μ P f hP hf hC a b) ?_ ?_ (hPx.abs.const_mul D) ?_).2
  · exact Eventually.of_forall (fun t => hP.aestronglyMeasurable.mul
      (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact hPx.aestronglyMeasurable.mul (hf'.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun x t _ => by
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hD (t * x + b)) (abs_nonneg (P x * x))])
  · exact ae_of_all _ (fun x t _ => by
      convert ((hd (t * x + b)).comp t (((hasDerivAt_id t).mul_const x).add_const b)).const_mul (P x) using 1
      · rfl
      · ring)

lemma abs_sech_sq_le_one (y : ℝ) : |sech y ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sech_pos y, sech_le_one y]

lemma abs_tanh_sech_sq_le_one (y : ℝ) : |Real.tanh y * sech y ^ 2| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_tanh_lt_one y).le).trans
    (abs_sech_sq_le_one y)

lemma abs_sech_sq_derivative_le_two (y : ℝ) : |-2 * Real.tanh y * sech y ^ 2| ≤ 2 := by
  rw [show -2 * Real.tanh y * sech y ^ 2 = -2 * (Real.tanh y * sech y ^ 2) by ring, abs_mul]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_tanh_sech_sq_le_one y]

lemma integrable_affine_product (m r : ℝ) (v : NNReal) :
    Integrable (fun x : ℝ => (x + r) * x) (gaussianReal m v) := by
  have h := (IsGaussian.memLp_two_id.integrable_sq (μ := gaussianReal m v)).add
    (IsGaussian.integrable_id.const_mul r)
  convert h using 1
  ext x
  dsimp only [id_eq, Pi.add_apply]
  ring

lemma hasDerivAt_tanh_average (a r : ℝ) :
    HasDerivAt (fun t => ∫ x, Real.tanh (t * x) ∂gaussianReal r 1)
      (∫ x, x * sech (a * x) ^ 2 ∂gaussianReal r 1) a := by
  have h := hasDerivAt_weighted_integral (gaussianReal r 1) (fun _ => 1) Real.tanh
    (fun y => sech y ^ 2) (integrable_const 1)
    (by
      convert (IsGaussian.integrable_id (μ := gaussianReal r 1)) using 1
      ext x
      simp)
    (by fun_prop) hasDerivAt_tanh (fun y => (Real.abs_tanh_lt_one y).le)
    abs_sech_sq_le_one a 0
  simpa using h

lemma hasDerivAt_sech_average (a r : ℝ) :
    HasDerivAt (fun t => ∫ x, (x + r) * sech (t * x) ^ 2 ∂gaussianReal r 1)
      (∫ x, (x + r) * x * (-2 * Real.tanh (a * x) * sech (a * x) ^ 2) ∂gaussianReal r 1) a := by
  have hi : Integrable (fun x : ℝ => x + r) (gaussianReal r 1) :=
    IsGaussian.integrable_id.add (integrable_const r)
  have h := hasDerivAt_weighted_integral (gaussianReal r 1) (fun x => x + r)
    (fun y => sech y ^ 2) (fun y => -2 * Real.tanh y * sech y ^ 2) hi
    (integrable_affine_product r r 1) (by fun_prop) hasDerivAt_sech_sq
    abs_sech_sq_le_one abs_sech_sq_derivative_le_two a 0
  simpa using h

noncomputable def radialForce (a r : ℝ) : ℝ :=
  2 * a * (∫ x, Real.tanh (a * x) ∂gaussianReal r 1) +
    a ^ 2 * (∫ x, (x + r) * sech (a * x) ^ 2 ∂gaussianReal r 1)

lemma hasDerivAt_radialForce_raw (a r : ℝ) :
    HasDerivAt (fun t => radialForce t r)
      (2 * (∫ x, Real.tanh (a * x) ∂gaussianReal r 1) +
        2 * a * (∫ x, x * sech (a * x) ^ 2 ∂gaussianReal r 1) +
        2 * a * (∫ x, (x + r) * sech (a * x) ^ 2 ∂gaussianReal r 1) +
        a ^ 2 * (∫ x, (x + r) * x * (-2 * Real.tanh (a * x) * sech (a * x) ^ 2)
          ∂gaussianReal r 1)) a := by
  convert (((hasDerivAt_id a).const_mul 2).mul (hasDerivAt_tanh_average a r)).add
    (((hasDerivAt_id a).pow 2).mul (hasDerivAt_sech_average a r)) using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    ring

noncomputable def steinCorrection (a x : ℝ) : ℝ :=
  -a * (2 * sech (a * x) ^ 2 * (1 - (a * x) * Real.tanh (a * x)))

lemma hasDerivAt_steinCorrection (a x : ℝ) :
    HasDerivAt (steinCorrection a) (a ^ 2 * kernelW (a * x)) x := by
  convert ((hasDerivAt_kernelU_prime (a * x)).comp x
    ((hasDerivAt_id x).const_mul a)).const_mul (-a) using 1
  · rfl
  · ring

lemma force_derivative_decomposition (a r x : ℝ) :
    2 * Real.tanh (a * x) + 2 * a * (x * sech (a * x) ^ 2) +
      2 * a * ((x + r) * sech (a * x) ^ 2) +
      a ^ 2 * ((x + r) * x * (-2 * Real.tanh (a * x) * sech (a * x) ^ 2)) =
    2 * kernelV (a * x) + (x - r) * steinCorrection a x := by
  unfold kernelV steinCorrection
  ring

lemma integrable_weighted_correction (μ : Measure ℝ) (P : ℝ → ℝ)
    (hP : Integrable P μ) (hPx : Integrable (fun x => P x * x) μ) (a : ℝ) :
    Integrable (fun x => P x * steinCorrection a x) μ := by
  have h1 := integrable_weighted_bounded μ P (fun y => sech y ^ 2) hP
    (by fun_prop) abs_sech_sq_le_one a 0
  have h2 := integrable_weighted_bounded μ (fun x => P x * x)
    (fun y => Real.tanh y * sech y ^ 2) hPx (by fun_prop) abs_tanh_sech_sq_le_one a 0
  convert (h1.const_mul (-2 * a)).add (h2.const_mul (2 * a ^ 2)) using 1
  ext x
  simp only [Pi.add_apply, add_zero]
  unfold steinCorrection
  ring

lemma integrable_correction (a r : ℝ) : Integrable (steinCorrection a) (gaussianReal r 1) := by
  have hx : Integrable (fun x : ℝ => 1 * x) (gaussianReal r 1) := by
    convert (IsGaussian.integrable_id (μ := gaussianReal r 1)) using 1
    ext x
    simp
  simpa using integrable_weighted_correction (gaussianReal r 1) (fun _ => 1) (integrable_const 1) hx a

lemma integrable_shifted_correction (a r : ℝ) :
    Integrable (fun x => (x - r) * steinCorrection a x) (gaussianReal r 1) := by
  have hi : Integrable (fun x : ℝ => x - r) (gaussianReal r 1) :=
    IsGaussian.integrable_id.sub (integrable_const r)
  have hx : Integrable (fun x : ℝ => (x - r) * x) (gaussianReal r 1) := by
    simpa only [sub_eq_add_neg] using integrable_affine_product r (-r) 1
  exact integrable_weighted_correction (gaussianReal r 1) (fun x => x - r) hi hx a

lemma integral_correction_stein (a r : ℝ) :
    (∫ x, a ^ 2 * kernelW (a * x) ∂gaussianReal r 1) =
      ∫ x, (x - r) * steinCorrection a x ∂gaussianReal r 1 := by
  exact gaussian_stein r (steinCorrection a) (fun x => a ^ 2 * kernelW (a * x))
    (hasDerivAt_steinCorrection a) (integrable_correction a r)
    ((gaussian_integrable_scale r a kernelW (integrable_kernelW_gaussian _ _)).const_mul (a ^ 2))
    (integrable_shifted_correction a r)

lemma hasDerivAt_radialForce (a r : ℝ) :
    HasDerivAt (fun t => radialForce t r)
      (∫ x, kernelDerivative a x ∂gaussianReal r 1) a := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal r 1) := IsGaussian.integrable_id
  have hip : Integrable (fun x : ℝ => x + r) (gaussianReal r 1) := hi.add (integrable_const r)
  have h0 : Integrable (fun x => Real.tanh (a * x)) (gaussianReal r 1) := by
    simpa using integrable_weighted_bounded (gaussianReal r 1) (fun _ => 1) Real.tanh
      (integrable_const 1) (by fun_prop) (fun y => (Real.abs_tanh_lt_one y).le) a 0
  have h1 : Integrable (fun x => x * sech (a * x) ^ 2) (gaussianReal r 1) := by
    simpa using integrable_weighted_bounded (gaussianReal r 1) (fun x => x)
      (fun y => sech y ^ 2) hi (by fun_prop) abs_sech_sq_le_one a 0
  have h2 : Integrable (fun x => (x + r) * sech (a * x) ^ 2) (gaussianReal r 1) := by
    simpa using integrable_weighted_bounded (gaussianReal r 1) (fun x => x + r)
      (fun y => sech y ^ 2) hip (by fun_prop) abs_sech_sq_le_one a 0
  have h3 : Integrable (fun x => (x + r) * x * (-2 * Real.tanh (a * x) * sech (a * x) ^ 2))
      (gaussianReal r 1) := by
    simpa using integrable_weighted_bounded (gaussianReal r 1) (fun x => (x + r) * x)
      (fun y => -2 * Real.tanh y * sech y ^ 2) (integrable_affine_product r r 1)
      (by fun_prop) abs_sech_sq_derivative_le_two a 0
  have hv := (gaussian_integrable_scale r a kernelV (integrable_kernelV_gaussian _ _)).const_mul 2
  have hw := (gaussian_integrable_scale r a kernelW (integrable_kernelW_gaussian _ _)).const_mul (a ^ 2)
  have he : (∫ x, kernelDerivative a x ∂gaussianReal r 1) =
      2 * (∫ x, Real.tanh (a * x) ∂gaussianReal r 1) +
        2 * a * (∫ x, x * sech (a * x) ^ 2 ∂gaussianReal r 1) +
        2 * a * (∫ x, (x + r) * sech (a * x) ^ 2 ∂gaussianReal r 1) +
        a ^ 2 * (∫ x, (x + r) * x * (-2 * Real.tanh (a * x) * sech (a * x) ^ 2)
          ∂gaussianReal r 1) := by
    unfold kernelDerivative
    rw [integral_add hv hw, integral_correction_stein,
      ← integral_add hv (integrable_shifted_correction a r)]
    simp_rw [← force_derivative_decomposition]
    erw [integral_add (((h0.const_mul 2).add (h1.const_mul (2 * a))).add (h2.const_mul (2 * a)))
      (h3.const_mul (a ^ 2)), integral_add ((h0.const_mul 2).add (h1.const_mul (2 * a)))
      (h2.const_mul (2 * a)), integral_add (h0.const_mul 2) (h1.const_mul (2 * a))]
    simp only [integral_const_mul]
  exact (hasDerivAt_radialForce_raw a r).congr_deriv he.symm

lemma radialForce_derivative_lower {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    min a 1 * min r 1 / 60 ≤ deriv (fun t => radialForce t r) a := by
  rw [(hasDerivAt_radialForce a r).deriv]
  exact LongTails.Proofs.SymmetricReverseFisherTails.kernelDerivative_lower ha hr

lemma min_linear_lower {S x : ℝ} (hS : 0 < S) (hx : 0 ≤ x) (hxS : x ≤ S) :
    x * min S 1 / S ≤ min x 1 := by
  apply (div_le_iff₀ hS).mpr
  by_cases hS1 : S ≤ 1
  · rw [min_eq_left hS1, min_eq_left (hxS.trans hS1)]
  · rw [min_eq_right (le_of_not_ge hS1)]
    by_cases hx1 : x ≤ 1
    · rw [min_eq_left hx1]
      nlinarith [mul_nonneg hx (show 0 ≤ S - 1 by linarith)]
    · rw [min_eq_right (le_of_not_ge hx1)]
      simpa using hxS

lemma radialForce_increment_lower {a b r : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hr : 0 < r) :
    min r 1 * min (a + b) 1 * (a - b) / 120 ≤ radialForce a r - radialForce b r := by
  by_cases heq : b = a
  · subst b
    simp
  have hlt : b < a := lt_of_le_of_ne hba heq
  have hS : 0 < a + b := by linarith
  let C := min r 1 * min (a + b) 1 / (60 * (a + b))
  let F := fun x => radialForce x r - (C / 2) * x ^ 2
  have hc (x : ℝ) (hx : x ∈ Icc b a) : C * x ≤ min x 1 * min r 1 / 60 := by
    have hx0 : 0 ≤ x := hb.trans hx.1
    have hxS : x ≤ a + b := by linarith [hx.2]
    have h := mul_le_mul_of_nonneg_right (min_linear_lower hS hx0 hxS)
      (show 0 ≤ min r 1 / 60 by positivity)
    have he : C * x = x * min (a + b) 1 / (a + b) * (min r 1 / 60) := by
      dsimp [C]
      field_simp
    rw [he]
    convert h using 1
    ring
  have hd (x : ℝ) : HasDerivAt F
      ((∫ y, kernelDerivative x y ∂gaussianReal r 1) - C * x) x := by
    convert (hasDerivAt_radialForce x r).sub (((hasDerivAt_id x).pow 2).const_mul (C / 2)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : MonotoneOn F (Icc b a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b a)
      (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Ioo b a := by simpa using hx
    have hk := LongTails.Proofs.SymmetricReverseFisherTails.kernelDerivative_lower
      (show 0 < x by linarith [hx'.1]) hr
    linarith [hc x ⟨hx'.1.le, hx'.2.le⟩]
  have h := hm (show b ∈ Icc b a from ⟨le_rfl, hba⟩)
    (show a ∈ Icc b a from ⟨hba, le_rfl⟩) hba
  have he : C / 2 * a ^ 2 - C / 2 * b ^ 2 = min r 1 * min (a + b) 1 * (a - b) / 120 := by
    dsimp [C]
    field_simp
    ring
  dsimp only [F] at h
  linarith

lemma hasDerivAt_translated_integral (μ : Measure ℝ) (P f f' : ℝ → ℝ) {C D : ℝ}
    (hP : Integrable P μ) (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (a b : ℝ) :
    HasDerivAt (fun t => ∫ x, P x * f (a * x + t) ∂μ)
      (∫ x, P x * f' (a * x + b) ∂μ) b := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => P x * f (a * x + t))
    (F' := fun t x => P x * f' (a * x + t))
    (bound := fun x => D * |P x|) (s := univ) (by simp)
    ?_ (integrable_weighted_bounded μ P f hP hf hC a b) ?_ ?_ (hP.abs.const_mul D) ?_).2
  · exact Eventually.of_forall (fun t => hP.aestronglyMeasurable.mul
      (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact hP.aestronglyMeasurable.mul (hf'.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun x t _ => by
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hD (a * x + t)) (abs_nonneg (P x))])
  · exact ae_of_all _ (fun x t _ => by
      convert ((hd (a * x + t)).comp t ((hasDerivAt_id t).const_add (a * x))).const_mul (P x) using 1 <;> simp)

lemma gaussian_location_integral (v : NNReal) (c : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂gaussianReal c v) = ∫ z, f (z + c) ∂gaussianReal 0 v := by
  have hm := gaussianReal_map_add_const (μ := 0) (v := v) c
  rw [zero_add] at hm
  rw [← hm, integral_map (by fun_prop) hf.aestronglyMeasurable]

lemma hasDerivAt_gaussian_location_integral (v : NNReal) (f f' : ℝ → ℝ) {C D : ℝ}
    (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (c : ℝ) :
    HasDerivAt (fun t => ∫ y, f y ∂gaussianReal t v)
      (∫ y, f' y ∂gaussianReal c v) c := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  have h := hasDerivAt_translated_integral (gaussianReal 0 v) (fun _ => 1) f f'
    (integrable_const 1) hf' hd hC hD 1 c
  simp only [one_mul] at h
  simp_rw [gaussian_location_integral v _ f hf.measurable]
  rw [gaussian_location_integral v c f' hf'.measurable]
  exact h
lemma hasDerivAt_quadratic_integral (f f' : ℝ → ℝ) {C D : ℝ}
    (hf' : Continuous f') (hd : ∀ y, HasDerivAt f (f' y) y)
    (hC : ∀ y, |f y| ≤ C) (hD : ∀ y, |f' y| ≤ D) (r : ℝ) :
    HasDerivAt (fun t => ∫ x, f (t * x + t ^ 2) ∂gaussianReal 0 1)
      (∫ x, (x + 2 * r) * f' (r * x + r ^ 2) ∂gaussianReal 0 1) r := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  have hD0 : 0 ≤ D := (abs_nonneg (f' 0)).trans (hD 0)
  have hi : Integrable (fun x => f (r * x + r ^ 2)) (gaussianReal 0 1) := by
    simpa using integrable_weighted_bounded (gaussianReal 0 1) (fun _ => 1) f
      (integrable_const 1) hf hC r (r ^ 2)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => f (t * x + t ^ 2))
    (F' := fun t x => (x + 2 * t) * f' (t * x + t ^ 2))
    (bound := fun x => D * (|x| + 2 * (|r| + 1)))
    (s := Ioo (r - 1) (r + 1)) (Ioo_mem_nhds (by linarith) (by linarith))
    ?_ hi ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun t => (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact ((continuous_id.add continuous_const).mul (hf'.comp (by fun_prop))).aestronglyMeasurable
  · exact ae_of_all _ (fun x t ht => by
      have ht' : |t| ≤ |r| + 1 := abs_le.mpr ⟨by linarith [neg_abs_le r, ht.1], by linarith [le_abs_self r, ht.2]⟩
      have hx : |x + 2 * t| ≤ |x| + 2 * (|r| + 1) := by
        have h := abs_add_le x (2 * t)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
        linarith
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ |x + 2 * t| * D := mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hx hD0])
  · exact (IsGaussian.integrable_id.abs.add (integrable_const (2 * (|r| + 1)))).const_mul D
  · exact ae_of_all _ (fun x t _ => by
      convert (hd (t * x + t ^ 2)).comp t (((hasDerivAt_id t).mul_const x).add ((hasDerivAt_id t).pow 2)) using 1
      · ext y
        simp only [Function.comp_apply, Pi.add_apply, Pi.pow_apply, id_eq]
      · simp only [id_eq]
        ring)
end LongTails.Proofs.SymmetricReverseFisherRadial
