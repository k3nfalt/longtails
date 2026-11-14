import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Metric
open scoped Convolution

namespace LongTails.Proofs.CompactMollification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def probability (φ : ContDiffBump (0 : E)) : ProbabilityMeasure E :=
  ⟨volume.withDensity (fun z => ENNReal.ofReal (φ.normed volume z)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (ae_of_all _ φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]⟩

noncomputable def noise (φ : ContDiffBump (0 : E)) (z : E) : E :=
  if ‖z‖ ≤ φ.rOut then z else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma noise_norm (φ : ContDiffBump (0 : E)) (z : E) : ‖noise φ z‖ ≤ φ.rOut := by
  unfold noise
  split_ifs with hz
  · exact hz
  · simpa using φ.rOut_pos.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma noise_measurable (φ : ContDiffBump (0 : E)) : Measurable (noise φ) :=
  measurable_id.ite (measurableSet_le measurable_norm measurable_const) measurable_const

lemma noise_ae_eq (φ : ContDiffBump (0 : E)) :
    noise φ =ᵐ[(probability φ : Measure E)] id := by
  change ∀ᵐ z ∂volume.withDensity (fun z => ENNReal.ofReal (φ.normed volume z)), noise φ z = z
  rw [ae_withDensity_iff φ.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with z hz
  have hn : φ.normed volume z ≠ 0 := by intro h; simp [h] at hz
  have hb : z ∈ ball (0 : E) φ.rOut := by
    rw [← φ.support_normed_eq (μ := volume)]
    exact hn
  have hnorm : ‖z‖ < φ.rOut := by simpa only [mem_ball, dist_zero_right] using hb
  have hnle := hnorm.le
  simp [noise, hnle]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def average (φ : ContDiffBump (0 : E)) (f : E → F) (x : E) : F :=
  ∫ z, f (x - noise φ z) ∂(probability φ : Measure E)

omit [CompleteSpace F] in
lemma average_eq_convolution (φ : ContDiffBump (0 : E)) (f : E → F) (x : E) :
    average φ f x = (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  unfold average
  rw [integral_congr_ae ((noise_ae_eq φ).mono (fun z hz => congrArg (fun w => f (x - w)) hz))]
  change (∫ z, f (x - z) ∂volume.withDensity (fun z => ENNReal.ofReal (φ.normed volume z))) = _
  rw [integral_withDensity_eq_integral_toReal_smul φ.continuous_normed.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply]

omit [CompleteSpace F] in
lemma average_contDiff (φ : ContDiffBump (0 : E)) (f : E → F) (hf : Continuous f) (n : ℕ∞) :
    ContDiff ℝ n (average φ f) := by
  have he : average φ f = φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f :=
    funext (average_eq_convolution φ f)
  rw [he]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.locallyIntegrable

omit [CompleteSpace F] in
lemma average_integrable (φ : ContDiffBump (0 : E)) (f : E → F) (hf : Continuous f) (x : E) :
    Integrable (fun z => f (x - noise φ z)) (probability φ : Measure E) := by
  have hc : Continuous (fun z => φ.normed volume z • f (x - z)) :=
    φ.continuous_normed.smul (hf.comp (continuous_const.sub continuous_id))
  have hs : HasCompactSupport (fun z => φ.normed volume z • f (x - z)) :=
    φ.hasCompactSupport_normed.smul_right
  have hi : Integrable (fun z => φ.normed volume z • f (x - z)) volume :=
    hc.integrable_of_hasCompactSupport hs
  have hj : Integrable (fun z => f (x - z)) (probability φ : Measure E) := by
    apply (integrable_withDensity_iff_integrable_smul₀'
      φ.continuous_normed.measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (φ.nonneg_normed _)] using hi
  exact hj.congr ((noise_ae_eq φ).mono (fun z hz => congrArg (fun w => f (x - w)) hz.symm))

omit [CompleteSpace F] in
lemma average_norm_bound (φ : ContDiffBump (0 : E)) (f : E → F) (hf : Continuous f)
    (G : ℝ) (hG : ∀ x, ‖f x‖ ≤ G) (x : E) : ‖average φ f x‖ ≤ G := by
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono (average_integrable φ f hf x).norm (integrable_const G)
    (fun z => hG (x - noise φ z))
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma average_convex (φ : ContDiffBump (0 : E)) (f : E → ℝ) (hf : Continuous f)
    (hc : ConvexOn ℝ univ f) : ConvexOn ℝ univ (average φ f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hp (z : E) : f ((a • x + b • y) - noise φ z) ≤
      a * f (x - noise φ z) + b * f (y - noise φ z) := by
    have hh := hc.2 (mem_univ (x - noise φ z)) (mem_univ (y - noise φ z)) ha hb hab
    have he : a • (x - noise φ z) + b • (y - noise φ z) =
        (a • x + b • y) - noise φ z := by
      calc
        _ = (a • x + b • y) - (a + b) • noise φ z := by
          simp only [smul_sub, add_smul]
          abel
        _ = _ := by rw [hab, one_smul]
    simpa only [he, smul_eq_mul] using hh
  have hh := integral_mono (average_integrable φ f hf (a • x + b • y))
    (((average_integrable φ f hf x).const_mul a).add ((average_integrable φ f hf y).const_mul b)) hp
  have he := integral_add ((average_integrable φ f hf x).const_mul a)
    ((average_integrable φ f hf y).const_mul b)
  simp only [Pi.add_apply] at hh
  rw [he, integral_const_mul, integral_const_mul] at hh
  exact hh

end LongTails.Proofs.CompactMollification
