import LongTails.Proofs.Clipping
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory

namespace OracleTemplate

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma integrable_clip {g : Ω → E} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C) :
    Integrable (fun z => clip C (g z)) P :=
  Integrable.of_bound ((measurable_clip C).comp hg).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun z => norm_clip_le hC (g z)))

omit [CompleteSpace E] in
lemma clipped_bias_bound {g : Ω → E} (hg : Measurable g) (hgi : Integrable g P)
    {u : E} (hmean : ∫ z, g z ∂P = u) {C p σ : ℝ} (hC : 0 < C) (hp : 1 ≤ p)
    (hu : ‖u‖ ≤ C / 2)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ p) P)
    (hm : (∫ z, ‖g z - u‖ ^ p ∂P) ≤ σ ^ p) :
    ‖(∫ z, clip C (g z) ∂P) - u‖ ≤ σ ^ p / (C / 2) ^ (p - 1) := by
  have hc := integrable_clip (P := P) hg hC.le
  have hb := norm_integral_le_of_norm_le (hmi.div_const ((C / 2) ^ (p - 1)))
    (f := fun z => clip C (g z) - g z)
    (Filter.Eventually.of_forall (fun z => by
      rw [norm_sub_rev]
      exact clip_residual_le_moment hC hp hu (g z)))
  rw [integral_sub hc hgi, hmean, integral_div] at hb
  exact hb.trans (div_le_div_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _))

omit [CompleteSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma clipped_second_moment_bound {g : Ω → E} (hg : Measurable g)
    {u : E} {C p σ : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (hp2 : p ≤ 2) (hu : ‖u‖ ≤ C)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ p) P)
    (hm : (∫ z, ‖g z - u‖ ^ p ∂P) ≤ σ ^ p) :
    (∫ z, ‖clip C (g z) - u‖ ^ 2 ∂P) ≤ (2 * C) ^ (2 - p) * σ ^ p := by
  have hbound : ∀ z, ‖clip C (g z) - u‖ ^ 2 ≤ (2 * C) ^ (2 - p) * ‖g z - u‖ ^ p :=
    fun z => norm_clip_sub_sq_le hC hp hp2 hu (g z)
  have hi : Integrable (fun z => ‖clip C (g z) - u‖ ^ 2) P := by
    apply (hmi.const_mul ((2 * C) ^ (2 - p))).mono'
    · exact (((measurable_clip C).comp hg).sub_const u).norm.pow_const 2 |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound z)
  have hb := integral_mono hi (hmi.const_mul ((2 * C) ^ (2 - p))) hbound
  rw [integral_const_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by positivity) _))

omit [CompleteSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma clipped_moment_integrable {g : Ω → E} (hg : Measurable g)
    {u : E} {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (hu : ‖u‖ ≤ C)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ p) P) :
    Integrable (fun z => ‖clip C (g z) - u‖ ^ p) P := by
  apply hmi.mono'
  · exact ((((measurable_clip C).comp hg).sub_const u).norm.pow_const p).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (norm_clip_sub_le hC hu (g z)) hp)

omit [CompleteSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma clipped_moment_bound {g : Ω → E} (hg : Measurable g)
    {u : E} {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (hu : ‖u‖ ≤ C)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ p) P) :
    (∫ z, ‖clip C (g z) - u‖ ^ p ∂P) ≤ ∫ z, ‖g z - u‖ ^ p ∂P :=
  integral_mono (clipped_moment_integrable hg hC hp hu hmi) hmi
    (fun z => Real.rpow_le_rpow (norm_nonneg _) (norm_clip_sub_le hC hu (g z)) hp)

end OracleTemplate
