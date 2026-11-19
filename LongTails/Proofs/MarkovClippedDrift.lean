import LongTails.Proofs.HeavyTailedClipping
import LongTails.Proofs.ProxLinearDualSensitivity
import LongTails.Proofs.NormalizedStormMoments
import LongTails.Proofs.HeavyTailedMarkovMixing

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MarkovClippedDrift

variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Z]

noncomputable def drift (γ C : ℝ) (u v : E) := γ / 2 * ‖clip C v‖ ^ 2 - ⟪clip C v, u⟫

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma drift_bound {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ C) (u v : E) :
    |drift γ C u v| ≤ γ / 2 * C ^ 2 + C * ‖u‖ := by
  have hc := norm_clip_le hC v
  have hs := pow_le_pow_left₀ (norm_nonneg _) hc 2
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ γ / 2 * ‖clip C v‖ ^ 2)]
  exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
    ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _)))

omit [CompleteSpace E] in
lemma drift_measurable (γ C : ℝ) : Measurable (Function.uncurry (drift (E := E) γ C)) := by
  have hc : Measurable (fun z : E × E => clip C z.2) := (measurable_clip C).comp measurable_snd
  exact ((hc.norm.pow_const 2).const_mul _).sub (hc.inner measurable_fst)

lemma stationary_drift {μ : Measure Z} [IsProbabilityMeasure μ] {g : Z → E} {u : E}
    (hg : Measurable g) (hi : Integrable g μ) (hmean : ∫ z, g z ∂μ = u)
    {ε σ C γ : ℝ} (_hε : 0 < ε) (hσ : 0 < σ) (hC : 0 < C)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 8) (hlarge : 8 * σ ≤ C) (heC : ε ≤ C / 8)
    (hbias : 2 * σ ^ 2 / C ≤ ε / 32) (hnoise : γ * σ ^ 2 ≤ ε ^ 2 / 512)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ 2) μ)
    (hm : (∫ z, ‖g z - u‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    (∫ z, drift γ C u (g z) ∂μ) ≤ ε ^ 2 / 16 - (3 * ε / 8) * ‖u‖ := by
  let v := fun z => clip C (g z)
  have hv : Measurable v := (measurable_clip C).comp hg
  have hvi : Integrable v μ := integrable_clip hg hC.le
  have hv2 : Integrable (fun z => ‖v z‖ ^ 2) μ := Integrable.of_bound
    (hv.norm.pow_const 2).aestronglyMeasurable (C ^ 2) (.of_forall fun z => by
      simpa using (pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hC.le (g z)) 2))
  change (∫ z, γ / 2 * ‖v z‖ ^ 2 - ⟪v z, u⟫ ∂μ) ≤ _
  rw [integral_sub (hv2.const_mul _) (hvi.inner_const u), integral_const_mul]
  have hinner : (∫ z, ⟪v z, u⟫ ∂μ) = ⟪∫ z, v z ∂μ, u⟫ := by
    simp_rw [real_inner_comm u _]
    rw [integral_inner hvi]
  rw [hinner]
  by_cases hu : ‖u‖ ≤ C / 2
  · have hI := clipped_bias_bound hg hi hmean hC (by norm_num : (1 : ℝ) ≤ 2) hu
      (by simpa using hmi) (by simpa using hm)
    have hdev : ‖(∫ z, v z ∂μ) - u‖ ≤ ε / 32 := by
      refine hI.trans ?_
      norm_num
      linarith [show σ ^ 2 / (C / 2) = 2 * σ ^ 2 / C by ring]
    have hdot := real_inner_le_norm (u - ∫ z, v z ∂μ) u
    rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_rev] at hdot
    have hd := hdot.trans (mul_le_mul_of_nonneg_right hdev (norm_nonneg _))
    have hV : (∫ z, ‖v z‖ ^ 2 ∂μ) ≤ 2 * σ ^ 2 + 2 * ‖u‖ ^ 2 := by
      have hpt (z : Z) : ‖v z‖ ^ 2 ≤ 2 * ‖g z - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
        have hc := norm_clip_sub_le hC.le (show ‖u‖ ≤ C by linarith) (g z)
        have hh := NormalizedStorm.sq_norm_add_le (v z - u) u
        rw [sub_add_cancel] at hh
        exact hh.trans (by linarith [pow_le_pow_left₀ (norm_nonneg _) hc 2])
      have hh := integral_mono hv2 ((hmi.const_mul 2).add (integrable_const _)) hpt
      simp only [Pi.add_apply] at hh
      rw [integral_add (hmi.const_mul 2) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul] at hh
      linarith
    have hV' := mul_le_mul_of_nonneg_left hV (show 0 ≤ γ / 2 by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) (sq_nonneg ‖u‖),
      sq_nonneg (‖u‖ - ε / 4), mul_nonneg _hε.le (norm_nonneg u), sq_nonneg ε]
  · have hsec := (NormalizedStorm.integral_norm_le_sqrt
        (hg.sub measurable_const).aestronglyMeasurable hmi).trans (Real.sqrt_le_sqrt hm)
    rw [Real.sqrt_sq hσ.le] at hsec
    have hdev : ‖(∫ z, v z ∂μ) - clip C u‖ ≤ σ := by
      have he : (∫ z, v z - clip C u ∂μ) = (∫ z, v z ∂μ) - clip C u := by
        rw [integral_sub hvi (integrable_const _), integral_const, probReal_univ, one_smul]
      rw [← he]
      exact (norm_integral_le_of_norm_le (hi.sub (integrable_const u)).norm
        (.of_forall fun z => ProxLinearDualSensitivity.clipping_nonexpansive hC.le (g z) u)).trans hsec
    have hdot := real_inner_le_norm (clip C u - ∫ z, v z ∂μ) u
    rw [inner_sub_left, norm_sub_rev] at hdot
    have hd := hdot.trans (mul_le_mul_of_nonneg_right hdev (norm_nonneg _))
    have hc : C / 2 * ‖u‖ ≤ ⟪clip C u, u⟫ := by
      unfold clip
      split_ifs with h
      · rw [real_inner_self_eq_norm_sq]
        nlinarith [mul_nonneg (norm_nonneg u) (show 0 ≤ ‖u‖ - C / 2 by linarith)]
      · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        have hn : 0 < ‖u‖ := by linarith
        field_simp
        nlinarith [mul_nonneg hC.le (sq_nonneg ‖u‖)]
    have hV := integral_mono hv2 (integrable_const (C ^ 2))
      (fun z => pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hC.le (g z)) 2)
    rw [integral_const, probReal_univ, one_smul] at hV
    have hγC := mul_le_mul_of_nonneg_right hγ1 (sq_nonneg C)
    have hsC := mul_le_mul_of_nonneg_right hlarge (norm_nonneg u)
    have he := mul_le_mul_of_nonneg_right heC (norm_nonneg u)
    nlinarith [mul_le_mul_of_nonneg_left hV (show 0 ≤ γ / 2 by positivity),
      mul_nonneg hC.le (show 0 ≤ ‖u‖ - C / 2 by linarith), sq_nonneg ε]

end LongTails.Proofs.MarkovClippedDrift
