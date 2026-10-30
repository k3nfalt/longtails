import LongTails.Algorithms.FiniteScaleConvolutionalSgd
import LongTails.Proofs.ClusteredConvolutionalPerceptronGeometry
import LongTails.Proofs.SoftQuadraticDynamics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry

open LongTails.Setups.FiniteScaleConvolutionalSgd
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift margin direction)
open LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
  (decode plusFeature minusFeature shift_axis)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

lemma algorithm_family (p : Public) (η scale : ℝ) (period : ℕ+)
    (hη : 0 < η) (hscale : 0 < scale) :
    family p (LongTails.Algorithms.FiniteScaleConvolutionalSgd.algorithm p η scale period) := by
  refine ⟨η, scale, period, id, id, hη, hscale, measurable_id, ?_,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  exact Measure.map_id

noncomputable def initialState (p : Public) (scale ε : ℝ) :
    ManySampleConvolutionalPerceptronDynamics.State (Features p.dimension) where
  a := p.initialMean
  q := ⟪axis p.dimension, p.initialReadout⟫ / scale
  t := p.initialDifference
  z := (scale * ε)⁻¹ •
    (p.initialReadout - ⟪axis p.dimension, p.initialReadout⟫ • axis p.dimension)

lemma start_decode (p : Public) (scale ε : ℝ) (hs : scale ≠ 0) (hε : ε ≠ 0) :
    start p scale = scale • decode ε (initialState p scale ε) := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [start, decode, initialState, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring
  · change p.initialReadout = scale •
      ((⟪axis p.dimension, p.initialReadout⟫ / scale) • axis p.dimension +
        ε • ((scale * ε)⁻¹ •
          (p.initialReadout - ⟪axis p.dimension, p.initialReadout⟫ • axis p.dimension)))
    have h₁ : scale * (⟪axis p.dimension, p.initialReadout⟫ / scale) =
        ⟪axis p.dimension, p.initialReadout⟫ := by field_simp
    have h₂ : scale * ε * (scale * ε)⁻¹ = 1 := by field_simp
    rw [smul_add, smul_smul, smul_smul, smul_smul, h₁, h₂, one_smul]
    module

lemma margin_homogeneous {d : ℕ} (b : Features d) (θ : Space d) (scale : ℝ) :
    margin .conv d b (scale • θ) = scale ^ 2 * margin .conv d b θ := by
  simp only [margin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]
  ring

lemma direction_homogeneous {d : ℕ} (b : Features d) (θ : Space d) (scale : ℝ) :
    direction .conv d b (scale • θ) = scale • direction .conv d b θ := by
  simp only [direction, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right,
    Prod.smul_mk, smul_add, smul_smul]

lemma sample_plus (p : Public) (data : Data p) (G : Geometry p data) (i : Fin p.count) :
    plusFeature (data i) = G.background i • axis p.dimension +
      p.contrast • plusFeature (G.defect i) := by
  have he : (Real.sqrt 2)⁻¹ * (2 * (G.background i / Real.sqrt 2)) = G.background i := by
    field_simp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold plusFeature
  rw [G.sample_eq i, shift_add, shift_smul, shift_axis, shift_smul]
  calc
    _ = ((Real.sqrt 2)⁻¹ * (2 * (G.background i / Real.sqrt 2))) • axis p.dimension +
        p.contrast • ((Real.sqrt 2)⁻¹ • (G.defect i + shift (G.defect i))) := by module
    _ = _ := by rw [he]

lemma sample_minus (p : Public) (data : Data p) (G : Geometry p data) (i : Fin p.count) :
    minusFeature (data i) = p.contrast • minusFeature (G.defect i) := by
  unfold minusFeature
  rw [G.sample_eq i, shift_add, shift_smul, shift_axis, shift_smul]
  module

lemma plus_centered (p : Public) (data : Data p) (G : Geometry p data) (i : Fin p.count) :
    ⟪axis p.dimension, plusFeature (G.defect i)⟫ = 0 := by
  simp only [plusFeature, real_inner_smul_right, inner_add_right,
    ManySampleConvolutionalPerceptronGeometry.axis_shift_inner, G.centered, add_zero, mul_zero]

lemma minus_centered (p : Public) (data : Data p) (G : Geometry p data) (i : Fin p.count) :
    ⟪axis p.dimension, minusFeature (G.defect i)⟫ = 0 := by
  simp only [minusFeature, real_inner_smul_right, inner_sub_right,
    ManySampleConvolutionalPerceptronGeometry.axis_shift_inner, sub_self, mul_zero]

lemma centered_decode_inner {d : ℕ} (f : Features d) (ε : ℝ)
    (x : ManySampleConvolutionalPerceptronDynamics.State (Features d))
    (hf : ⟪axis d, f⟫ = 0) :
    ⟪f, (decode ε x).2⟫ = ε * ⟪f, x.z⟫ := by
  have hh : ⟪f, axis d⟫ = 0 := by rw [real_inner_comm]; exact hf
  simp only [decode, inner_add_right, real_inner_smul_right, hh, mul_zero, zero_add]

lemma normalized_margin (p : Public) (data : Data p) (G : Geometry p data)
    (η : ℝ) (x : ManySampleConvolutionalPerceptronDynamics.State (Features p.dimension))
    (i : Fin p.count) (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    η * margin .conv p.dimension (data i) (decode (η * p.contrast) x) =
      (η * G.background i) * x.a * x.q + (η * p.contrast) ^ 2 *
        (x.a * ⟪plusFeature (G.defect i), x.z⟫ +
          x.t * ⟪minusFeature (G.defect i), x.z⟫) := by
  rw [ManySampleConvolutionalPerceptronGeometry.margin_decode,
    sample_plus p data G i, sample_minus p data G i, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
    ManySampleConvolutionalPerceptronGeometry.decode_axis hd hx,
    centered_decode_inner _ _ _ (plus_centered p data G i),
    centered_decode_inner _ _ _ (minus_centered p data G i)]
  ring

lemma physical_margin (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : η ≠ 0)
    (x : ManySampleConvolutionalPerceptronDynamics.State (Features p.dimension))
    (i : Fin p.count) (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    margin .conv p.dimension (data i) (scale • decode (η * p.contrast) x) =
      (scale ^ 2 / η) * ((η * G.background i) * x.a * x.q +
        (η * p.contrast) ^ 2 * (x.a * ⟪plusFeature (G.defect i), x.z⟫ +
          x.t * ⟪minusFeature (G.defect i), x.z⟫)) := by
  rw [margin_homogeneous, ← normalized_margin p data G η x i hd hx]
  field_simp

lemma margin_from_logistic_value (m : ℝ) :
    -Real.log (Real.exp (Real.log (1 + Real.exp (-m))) - 1) = m := by
  rw [Real.exp_log (by positivity : 0 < 1 + Real.exp (-m))]
  simp

lemma logistic_value_derivative (m : ℝ) :
    HasDerivAt (fun z : ℝ => Real.log (1 + Real.exp (-z)))
      (-SoftQuadraticDynamics.weight m) m := by
  have hh := (((hasDerivAt_id m).neg.exp).const_add 1).log
    (by positivity : (1 : ℝ) + Real.exp (-m) ≠ 0)
  convert hh using 1 <;> try rfl
  unfold SoftQuadraticDynamics.weight
  change -(1 / (1 + Real.exp m)) = Real.exp (-m) * (-1) / (1 + Real.exp (-m))
  have hp : 1 + Real.exp m ≠ 0 := by positivity
  have hn : 1 + Real.exp (-m) ≠ 0 := by positivity
  have he : Real.exp m * Real.exp (-m) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  nlinarith

noncomputable def pairing {d : ℕ} (θ : Space d) : Space d →L[ℝ] ℝ :=
  θ.1.1 • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Features d))) +
  θ.1.2 • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Features d))) +
  (innerSL ℝ θ.2).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Features d))

lemma pairing_apply {d : ℕ} (θ h : Space d) :
    pairing θ h = θ.1.1 * h.1.1 + θ.1.2 * h.1.2 + ⟪θ.2, h.2⟫ := by
  rfl

lemma margin_derivative {d : ℕ} (b : Features d) (θ : Space d) :
    HasFDerivAt (margin .conv d b) (pairing (direction .conv d b θ)) θ := by
  let f₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Features d))
  let f₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Features d))
  let v := ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Features d)
  have hh := ((f₁.hasFDerivAt (x := θ)).mul ((innerSL ℝ b).comp v).hasFDerivAt).add
    (f₂.hasFDerivAt.mul ((innerSL ℝ (shift b)).comp v).hasFDerivAt)
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  simp [pairing, direction, f₁, f₂, v]
  ring

lemma logistic_derivative {d : ℕ} (b : Features d) (θ : Space d) :
    HasFDerivAt (fun x => Real.log (1 + Real.exp (-margin .conv d b x)))
      (-SoftQuadraticDynamics.weight (margin .conv d b θ) •
        pairing (direction .conv d b θ)) θ := by
  exact (logistic_value_derivative (margin .conv d b θ)).comp_hasFDerivAt θ
    (margin_derivative b θ)

lemma feature_norm_identity {d : ℕ} (u : Features d) :
    ‖plusFeature u‖ ^ 2 + ‖minusFeature u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  have hh := parallelogram_law_with_norm ℝ u (shift u)
  rw [norm_shift] at hh
  simp only [plusFeature, minusFeature, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

lemma feature_norm_bounds {d : ℕ} (u : Features d) (hu : ‖u‖ ≤ (Real.sqrt 2)⁻¹) :
    ‖plusFeature u‖ ≤ 1 ∧ ‖minusFeature u‖ ≤ 1 := by
  have hsq := (sq_le_sq₀ (norm_nonneg u) (by positivity : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹)).2 hu
  rw [inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at hsq
  have hh := feature_norm_identity u
  constructor
  · nlinarith [sq_nonneg ‖minusFeature u‖]
  · nlinarith [sq_nonneg ‖plusFeature u‖]

lemma unit_remainder_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v u : E) (hv : ‖v‖ = 1) : ‖u - ⟪v, u⟫ • v‖ ≤ ‖u‖ := by
  have hh : ‖u - ⟪v, u⟫ • v‖ ^ 2 = ‖u‖ ^ 2 - ⟪v, u⟫ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [real_inner_comm u v]
    ring
  nlinarith [sq_nonneg ⟪v, u⟫, norm_nonneg u, norm_nonneg (u - ⟪v, u⟫ • v)]

lemma initialState_centered (p : Public) (scale ε : ℝ) (hd : 0 < p.dimension) :
    ⟪axis p.dimension, (initialState p scale ε).z⟫ = 0 := by
  simp only [initialState, real_inner_smul_right, inner_sub_right,
    ManySampleConvolutionalPerceptronGeometry.axis_inner hd, mul_one, sub_self, mul_zero]

lemma initialState_readout_bounds (p : Public) (scale ε : ℝ) (hd : 0 < p.dimension)
    (hs : 0 < scale) (hε : 0 < ε)
    (hhead : ‖p.initialReadout‖ ≤ scale) (hres : ‖p.initialReadout‖ ≤ scale * ε) :
    |(initialState p scale ε).q| ≤ 1 ∧ ‖(initialState p scale ε).z‖ ≤ 1 := by
  have haxis := ManySampleConvolutionalPerceptronGeometry.axis_norm hd
  constructor
  · change |⟪axis p.dimension, p.initialReadout⟫ / scale| ≤ 1
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).2
    have hh := abs_real_inner_le_norm (axis p.dimension) p.initialReadout
    rw [haxis, one_mul] at hh
    simpa using hh.trans hhead
  · change ‖(scale * ε)⁻¹ •
        (p.initialReadout - ⟪axis p.dimension, p.initialReadout⟫ • axis p.dimension)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hs hε))]
    calc
      _ ≤ (scale * ε)⁻¹ * (scale * ε) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_pos hs hε).le)
        exact (unit_remainder_norm_le _ _ haxis).trans hres
      _ = 1 := inv_mul_cancel₀ (mul_pos hs hε).ne'

end LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry
