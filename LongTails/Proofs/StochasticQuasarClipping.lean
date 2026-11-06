import LongTails.Proofs.GeneralNormClipping

open MeasureTheory

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma biased_clipping_moments {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → E} {g : E} {H β V : ℝ} (hH : 0 < H) (hg : ‖g‖ ≤ H / 2)
    (hm : Measurable Z) (hi : Integrable Z μ)
    (h2i : Integrable (fun ω => ‖Z ω - g‖ ^ 2) μ)
    (hb : ‖(∫ ω, Z ω ∂μ) - g‖ ≤ β)
    (h2 : (∫ ω, ‖Z ω - g‖ ^ 2 ∂μ) ≤ V) :
    Integrable (fun ω => clip H (Z ω)) μ ∧
      Integrable (fun ω => ‖clip H (Z ω) - g‖ ^ 2) μ ∧
      (∫ ω, ‖clip H (Z ω) - g‖ ^ 2 ∂μ) ≤ V ∧
      ‖(∫ ω, clip H (Z ω) ∂μ) - g‖ ≤ β + 2 * V / H ∧
      (∀ ω, ‖clip H (Z ω) - g‖ ≤ 2 * H) := by
  have hgH : ‖g‖ ≤ H := by linarith
  have hc := GeneralNormClipping.integrable_clip (P := μ) hm hH.le
  have hcm := (measurable_clip H).comp hm
  have hsq (ω : Ω) : ‖clip H (Z ω) - g‖ ^ 2 ≤ ‖Z ω - g‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_clip_sub_le hH.le hgH (Z ω)) 2
  have hc2 : Integrable (fun ω => ‖clip H (Z ω) - g‖ ^ 2) μ :=
    h2i.mono' ((hcm.sub_const g).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖clip H (Z ω) - g‖)]
        exact hsq ω))
  have hr (ω : Ω) : ‖Z ω - clip H (Z ω)‖ ≤ (2 / H) * ‖Z ω - g‖ ^ 2 := by
    have hh := clip_residual_le_moment hH (by norm_num : (1 : ℝ) ≤ 2) hg (Z ω)
    norm_num only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hh
    convert hh using 1; ring
  have hri := (hi.sub hc).norm
  have hri2 := h2i.const_mul (2 / H)
  have hriB := integral_mono hri hri2 hr
  rw [integral_const_mul] at hriB
  have hrv : (∫ ω, ‖Z ω - clip H (Z ω)‖ ∂μ) ≤ 2 * V / H := by
    have hh := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / H)
    exact hriB.trans (by convert hh using 1; ring)
  refine ⟨hc, hc2, (integral_mono hc2 h2i hsq).trans h2, ?_, ?_⟩
  · have ht := norm_integral_le_integral_norm (μ := μ) (fun ω => Z ω - clip H (Z ω))
    rw [integral_sub hi hc] at ht
    have he : (∫ ω, clip H (Z ω) ∂μ) - g =
        ((∫ ω, Z ω ∂μ) - g) - ((∫ ω, Z ω ∂μ) - ∫ ω, clip H (Z ω) ∂μ) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hb (ht.trans hrv))
  · intro ω
    have hh := norm_clip_le hH.le (Z ω)
    exact (norm_sub_le _ _).trans (by linarith)

end OracleTemplate.StochasticQuasar
