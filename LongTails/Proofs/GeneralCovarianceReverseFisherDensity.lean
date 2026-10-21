import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace NNReal ENNReal

namespace LongTails.Proofs.GeneralCovarianceReverseFisherDensity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

noncomputable def stdDensity (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : ℝ :=
  (2 * Real.pi) ^ (-(Module.finrank ℝ V / 2 : ℝ)) * Real.exp (-‖v‖ ^ 2 / 2)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma stdDensity_pos (v : V) : 0 < stdDensity V v := by
  unfold stdDensity
  have : 0 < 2 * Real.pi := by positivity
  positivity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_stdDensity : Continuous (stdDensity V) := by
  unfold stdDensity
  fun_prop

lemma integrable_exp_half_sq :
    Integrable (fun v : V => Real.exp (-‖v‖ ^ 2 / 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (1 / 2 : ℂ))
    (by norm_num) 0 0
  refine h.norm.congr (ae_of_all _ (fun v => ?_))
  have he : -(1 / 2 : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ⟪(0 : V), v⟫ = ((-‖v‖ ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [he, Complex.norm_exp_ofReal]

lemma integral_exp_half_sq :
    ∫ v : V, Real.exp (-‖v‖ ^ 2 / 2) = (2 * Real.pi) ^ (Module.finrank ℝ V / 2 : ℝ) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (b := 1 / 2) (by norm_num)
  convert h using 2
  · ext v; ring_nf
  · ring_nf

lemma integrable_stdDensity : Integrable (stdDensity V) := by
  unfold stdDensity
  exact integrable_exp_half_sq.const_mul _

lemma integral_stdDensity : ∫ v : V, stdDensity V v = 1 := by
  unfold stdDensity
  rw [integral_const_mul, integral_exp_half_sq, ← Real.rpow_add (by positivity)]
  simp

instance isProbabilityMeasure_withDensity_stdDensity :
    IsProbabilityMeasure (volume.withDensity (fun v : V => ENNReal.ofReal (stdDensity V v))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_stdDensity
      (ae_of_all _ (fun v => (stdDensity_pos v).le)), integral_stdDensity, ENNReal.ofReal_one]

lemma stdGaussian_eq_withDensity :
    stdGaussian V = volume.withDensity (fun v => ENNReal.ofReal (stdDensity V v)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul (continuous_stdDensity.measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hpt (x : V) : (ENNReal.ofReal (stdDensity V x)).toReal • cexp (⟪x, t⟫ * I) =
      (((2 * Real.pi) ^ (-(Module.finrank ℝ V / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 + I * ⟪t, x⟫) := by
    rw [ENNReal.toReal_ofReal (stdDensity_pos x).le, Complex.real_smul]
    unfold stdDensity
    push_cast
    rw [mul_assoc, ← Complex.exp_add, real_inner_comm]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num) I t]
  have h2 : (↑Real.pi / (1 / 2 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have h3 : ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, h3, ← Complex.ofReal_cpow (by positivity), ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (by positivity)]
  simp only [neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.I_sq]
  ring

noncomputable def gaussDensity (A : V ≃L[ℝ] V) (θ x : V) : ℝ :=
  |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| * stdDensity V (A.symm (x - θ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma det_ne_zero (A : V ≃L[ℝ] V) : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := by
  have h := LinearMap.det_comp (A : V →ₗ[ℝ] V) (A.symm : V →ₗ[ℝ] V)
  have hc : (A : V →ₗ[ℝ] V).comp (A.symm : V →ₗ[ℝ] V) = LinearMap.id := by
    ext x
    simp
  intro h0
  rw [hc, LinearMap.det_id, h0, zero_mul] at h
  exact one_ne_zero h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma gaussDensity_pos (A : V ≃L[ℝ] V) (θ x : V) : 0 < gaussDensity A θ x := by
  unfold gaussDensity
  have := det_ne_zero A
  have := stdDensity_pos (A.symm (x - θ))
  positivity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_gaussDensity (A : V ≃L[ℝ] V) (θ : V) : Continuous (gaussDensity A θ) := by
  unfold gaussDensity
  exact continuous_const.mul (continuous_stdDensity.comp (by fun_prop))

lemma map_volume_equiv (A : V ≃L[ℝ] V) :
    Measure.map A (volume : Measure V) =
      ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • volume :=
  Measure.map_linearMap_addHaar_eq_smul_addHaar volume (det_ne_zero A)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_affine (A : V ≃L[ℝ] V) (θ : V) (F : V → E) :
    ∫ z, F (θ + A z) ∂stdGaussian V = ∫ x, gaussDensity A θ x • F x := by
  let e : V ≃ᵐ V := A.toHomeomorph.toMeasurableEquiv
  have he : (e : V → V) = A := rfl
  let h : V → E := fun y => stdDensity V (A.symm y) • F (θ + y)
  calc
    _ = ∫ z, stdDensity V z • F (θ + A z) := by
      rw [stdGaussian_eq_withDensity,
        integral_withDensity_eq_integral_toReal_smul
          (continuous_stdDensity.measurable.ennreal_ofReal)
          (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      simp_rw [ENNReal.toReal_ofReal (stdDensity_pos _).le]
    _ = ∫ z, h (e z) := by
      congr 1
      ext z
      simp [h, he]
    _ = ∫ y, h y ∂Measure.map e volume := (integral_map_equiv e h).symm
    _ = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ y, h y := by
      rw [show (Measure.map e volume) = Measure.map A volume from rfl, map_volume_equiv,
        integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
    _ = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ x, h (x - θ) := by
      rw [integral_sub_right_eq_self h θ]
    _ = _ := by
      rw [← integral_smul]
      congr 1
      ext x
      simp only [h, gaussDensity, smul_smul, add_sub_cancel]

lemma integrable_affine_iff (A : V ≃L[ℝ] V) (θ : V) (F : V → E) :
    Integrable (fun z => F (θ + A z)) (stdGaussian V) ↔
      Integrable (fun x => gaussDensity A θ x • F x) := by
  let e : V ≃ᵐ V := A.toHomeomorph.toMeasurableEquiv
  have he : (e : V → V) = A := rfl
  let h : V → E := fun y => stdDensity V (A.symm y) • F (θ + y)
  have hd : |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| ≠ 0 := by
    simpa using det_ne_zero A
  calc
    _ ↔ Integrable (fun z => stdDensity V z • F (θ + A z)) := by
      rw [stdGaussian_eq_withDensity,
        integrable_withDensity_iff_integrable_smul'
          (continuous_stdDensity.measurable.ennreal_ofReal)
          (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      simp_rw [ENNReal.toReal_ofReal (stdDensity_pos _).le]
    _ ↔ Integrable (h ∘ e) := by
      apply integrable_congr
      exact ae_of_all _ (fun z => by simp [h, he])
    _ ↔ Integrable h (Measure.map e volume) := (e.measurableEmbedding.integrable_map_iff).symm
    _ ↔ Integrable h := by
      rw [show (Measure.map e volume) = Measure.map A volume from rfl, map_volume_equiv]
      exact integrable_smul_measure (by simpa using hd) ENNReal.ofReal_ne_top
    _ ↔ Integrable (fun x => h (x - θ)) := by
      constructor
      · intro hh
        exact hh.comp_sub_right θ
      · intro hh
        have := hh.comp_sub_right (-θ)
        simpa using this
    _ ↔ _ := by
      rw [← integrable_smul_iff hd]
      apply integrable_congr
      exact ae_of_all _ (fun x => by
        simp only [h, gaussDensity, Pi.smul_apply, smul_smul, add_sub_cancel])

lemma integrable_exp_neg_mul_sq (c : ℝ) (hc : 0 < c) :
    Integrable (fun v : V => Real.exp (-c * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (c : ℂ))
    (by simpa using hc) 0 0
  refine h.norm.congr (ae_of_all _ (fun v => ?_))
  have he : -(c : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ⟪(0 : V), v⟫ = ((-c * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [he, Complex.norm_exp_ofReal]

lemma integrable_exp_quad (A : V ≃L[ℝ] V) (θ : V) (c : ℝ) (hc : 0 < c) :
    Integrable (fun x => Real.exp (-c * ‖A.symm (x - θ)‖ ^ 2)) := by
  let e : V ≃ᵐ V := A.symm.toHomeomorph.toMeasurableEquiv
  have he : (e : V → V) = A.symm := rfl
  let g : V → ℝ := fun v => Real.exp (-c * ‖v‖ ^ 2)
  have hg : Integrable g (Measure.map e volume) := by
    rw [show (Measure.map e volume) = Measure.map A.symm volume from rfl, map_volume_equiv]
    exact (integrable_exp_neg_mul_sq c hc).smul_measure ENNReal.ofReal_ne_top
  have h1 : Integrable (g ∘ e) := (e.measurableEmbedding.integrable_map_iff).mp hg
  have h2 := h1.comp_sub_right θ
  refine h2.congr (ae_of_all _ (fun x => ?_))
  simp [g, he]

end LongTails.Proofs.GeneralCovarianceReverseFisherDensity
