import LongTails.Proofs.DistributedNormalizedMessages
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace LongTails.Proofs.DistributedCompressionIntegration

lemma product_second_moment {Ω Θ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Q : Measure Θ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : Ω → Θ → E) (H : Ω → ℝ) (hZ : Measurable (Function.uncurry Z))
    (hZ2 : ∀ ω, Integrable (fun θ => ‖Z ω θ‖ ^ 2) Q) (hH : Integrable H P)
    (hbound : ∀ ω, (∫ θ, ‖Z ω θ‖ ^ 2 ∂Q) ≤ H ω) :
    Integrable (Function.uncurry Z) (P.prod Q) ∧
      Integrable (fun z : Ω × Θ => ‖Z z.1 z.2‖ ^ 2) (P.prod Q) ∧
      (∫ z : Ω × Θ, ‖Z z.1 z.2‖ ^ 2 ∂P.prod Q) ≤ ∫ ω, H ω ∂P := by
  have hf : Measurable (fun z : Ω × Θ => ‖Z z.1 z.2‖ ^ 2) := hZ.norm.pow_const 2
  have hKm : AEStronglyMeasurable (fun ω => ∫ θ, ‖Z ω θ‖ ^ 2 ∂Q) P :=
    (hf.aestronglyMeasurable (μ := P.prod Q)).integral_prod_right'
  have hKi : Integrable (fun ω => ∫ θ, ‖Z ω θ‖ ^ 2 ∂Q) P := by
    apply hH.mono' hKm
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact hbound ω
  have hi : Integrable (fun z : Ω × Θ => ‖Z z.1 z.2‖ ^ 2) (P.prod Q) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hZ2, ?_⟩
    simpa only [Real.norm_eq_abs, abs_sq] using hKi
  have hbig : Integrable (fun z : Ω × Θ => 1 + ‖Z z.1 z.2‖ ^ 2) (P.prod Q) :=
    (integrable_const 1).add hi
  have hZi : Integrable (Function.uncurry Z) (P.prod Q) := by
    apply hbig.mono' hZ.aestronglyMeasurable
    filter_upwards [] with z
    change ‖Z z.1 z.2‖ ≤ 1 + ‖Z z.1 z.2‖ ^ 2
    nlinarith [sq_nonneg (‖Z z.1 z.2‖ - 1 / 2)]
  refine ⟨hZi, hi, ?_⟩
  rw [integral_prod _ hi]
  exact integral_mono hKi hH hbound

lemma product_centered_moments {Ω Θ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Q : Measure Θ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (W : Ω → Θ → E) (v : ℝ) (hm : Measurable (Function.uncurry W))
    (h2 : ∀ z, Integrable (fun θ => ‖W z θ‖ ^ 2) Q)
    (h0 : ∀ z, (∫ θ, W z θ ∂Q) = 0)
    (hv : ∀ z, (∫ θ, ‖W z θ‖ ^ 2 ∂Q) ≤ v) :
    Integrable (Function.uncurry W) (P.prod Q) ∧
      (∫ z, W z.1 z.2 ∂P.prod Q) = 0 ∧
      Integrable (fun z => ‖W z.1 z.2‖ ^ 2) (P.prod Q) ∧
      (∫ z, ‖W z.1 z.2‖ ^ 2 ∂P.prod Q) ≤ v := by
  obtain ⟨hi, hi2, hbound⟩ := product_second_moment P Q W (fun _ => v) hm h2 (integrable_const v) hv
  refine ⟨hi, ?_, hi2, ?_⟩
  · change (∫ z, Function.uncurry W z ∂P.prod Q) = 0
    rw [integral_prod _ hi]
    simp only [Function.uncurry, h0, integral_zero]
  · simpa only [integral_const, probReal_univ, one_smul] using hbound

lemma compressed_clipped_batch_moments {Ω Θ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Q : Measure Θ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Y : Ω → E) (C : E → Θ → E) (g : E) {G a ω δ : ℝ}
    (hG : 0 ≤ G) (ha : 0 < a) (hω : 0 ≤ ω) (hg : ‖g‖ ≤ G)
    (hYm : Measurable Y) (hYi : Integrable Y P)
    (hY2 : Integrable (fun z => ‖Y z - g‖ ^ 2) P) (hmean : (∫ z, Y z ∂P) = g)
    (hCm : Measurable (Function.uncurry C))
    (hC : ∀ c, ‖c‖ ≤ G + a → Integrable (C c) Q ∧ (∫ θ, C c θ ∂Q) = c ∧
      Integrable (fun θ => ‖C c θ - c‖ ^ 2) Q ∧
      (∫ θ, ‖C c θ - c‖ ^ 2 ∂Q) ≤ ω * ‖c‖ ^ 2 + δ) :
    let S := fun z : Ω × Θ => C (OracleTemplate.clip (G + a) (Y z.1)) z.2
    Integrable S (P.prod Q) ∧
      Integrable (fun z => ‖S z - g‖ ^ 2) (P.prod Q) ∧
      (∫ z, ‖S z - g‖ ^ 2 ∂P.prod Q) ≤
        (1 + ω) * (∫ z, ‖Y z - g‖ ^ 2 ∂P) + ω * ‖g‖ ^ 2 + δ ∧
      ‖(∫ z, S z ∂P.prod Q) - g‖ ≤ (∫ z, ‖Y z - g‖ ^ 2 ∂P) / (4 * a) := by
  intro S
  let c := fun z => OracleTemplate.clip (G + a) (Y z)
  have hB : 0 ≤ G + a := by positivity
  have hcm : Measurable c := (OracleTemplate.measurable_clip (G + a)).comp hYm
  have hc (z : Ω) := hC (c z) (OracleTemplate.norm_clip_le hB (Y z))
  have hSm : Measurable S := hCm.comp ((hcm.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨hci2, hcv⟩ := DistributedNormalizedMessages.clipped_batch_second_moment hB
    (g := g) (by linarith) hYm.aestronglyMeasurable hY2
  obtain ⟨hcni, hcnv⟩ := DistributedNormalizedMessages.clipped_batch_norm_second_moment hB
    hYm.aestronglyMeasurable hYi hY2 hmean
  have hcond (z : Ω) := DistributedNormalizedMessages.unbiased_compression_shift (c z) g
    (hc z).1 (hc z).2.2.1 (hc z).2.1 (hc z).2.2.2
  let H := fun z => ‖c z - g‖ ^ 2 + ω * ‖c z‖ ^ 2 + δ
  have hHi : Integrable H P := (hci2.add (hcni.const_mul ω)).add (integrable_const δ)
  have hZm : Measurable (Function.uncurry (fun z θ => S (z, θ) - g)) := hSm.sub_const g
  obtain ⟨hZi, hZ2, hZv⟩ := product_second_moment P Q (fun z θ => S (z, θ) - g) H hZm
    (fun z => (hcond z).1) hHi (fun z => by simpa only [H, add_assoc] using (hcond z).2)
  have hSi : Integrable S (P.prod Q) := by
    convert hZi.add (integrable_const g) using 1
    funext z
    simp [Function.uncurry]
  have hpart : Integrable (fun z => ‖c z - g‖ ^ 2 + ω * ‖c z‖ ^ 2) P :=
    hci2.add (hcni.const_mul ω)
  have hHbound : (∫ z, H z ∂P) ≤
      (1 + ω) * (∫ z, ‖Y z - g‖ ^ 2 ∂P) + ω * ‖g‖ ^ 2 + δ := by
    change (∫ z, (‖c z - g‖ ^ 2 + ω * ‖c z‖ ^ 2) + δ ∂P) ≤ _
    rw [integral_add hpart (integrable_const δ),
      integral_add hci2 (hcni.const_mul ω), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    nlinarith [mul_le_mul_of_nonneg_left hcnv hω]
  have hmeanS : (∫ z, S z ∂P.prod Q) = ∫ z, c z ∂P := by
    rw [integral_prod _ hSi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => (hc z).2.1)
  refine ⟨hSi, hZ2, hZv.trans hHbound, ?_⟩
  rw [hmeanS]
  exact DistributedNormalizedMessages.clipped_batch_bias hG ha hg hYm.aestronglyMeasurable
    hYi hY2 hmean

end LongTails.Proofs.DistributedCompressionIntegration
