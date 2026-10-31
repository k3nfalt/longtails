import LongTails.Proofs.GapNoiseStageDrift
import LongTails.Proofs.GapNoiseOuter
import LongTails.Proofs.MultiplicativeRobustConfidence

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapNoiseFinal

open OracleTemplate OracleTemplate.ConstrainedMonotone OracleTemplate.ProjectedClippedExtragradient

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma final_gap_bound {X : Set E} (t : Tuning) {F : E → E}
    (hF : GeneralizedMonotone.Hyp F t.L0 t.L1) (hR : 0 < t.R) (hε : 0 < t.ε)
    (anchor x p s : E) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : Normal X p (-(F p + regularization t (stageCount t - 1) • (p - anchor))))
    (hsolution : Normal X s (-F s))
    (hxp : ‖x - p‖ ≤ radius t (stageCount t - 1)) (hps : ‖p - s‖ ≤ t.R)
    (hFs : ‖F s‖ ≤ t.G) (hFp : ‖F p‖ ≤ rootBound t)
    (hbias : regularization t (stageCount t - 1) * ‖p - anchor‖ ≤ t.ε) :
    ⟪F x - F s, x - s⟫ ≤ 3 * t.ε * t.R := by
  let d := radius t (stageCount t - 1)
  let C := curvature t
  let c : LongTails.Algorithms.GapNoisePastExtragradient.StageConfig (E := E) :=
    ⟨t.L1, 32 * C, d, regularization t (stageCount t - 1), anchor, x⟩
  have h0 := hF.L0_pos
  have h1 := hF.L1_nonneg
  have hG := (norm_nonneg _).trans hFs
  have hC : 0 < C := curvature_pos t h0 h1 hR.le hG hε.le
  have hd : 0 < d := radius_pos t hR _
  have hdR : d ≤ t.R := radius_le t hR.le _
  have hCd : C * d ≤ t.ε / 2 ^ 20 := last_radius_curvature t hC.le hR hε
  have hlow := curvature_lower t h0.le h1 hR.le hG hε.le
  have hbd : t.L1 * d ≤ 1 / 2 ^ 20 := by
    have hh := mul_le_mul_of_nonneg_right hlow hd.le
    change (t.L0 + t.L1 * t.ε) * d ≤ C * d at hh
    nlinarith [mul_nonneg h0.le hd.le]
  have hbound := rootBound_curvature t h0.le h1 hR.le hG hε.le
  have hrootSlope : 2 * (t.L0 + t.L1 * ‖F p‖) ≤ 32 * C := by
    have hh := mul_le_mul_of_nonneg_left hFp h1
    change t.L0 + t.L1 * rootBound t + t.L1 * t.ε ≤ 16 * C at hbound
    nlinarith [mul_nonneg h1 hε.le]
  have hbase : t.L0 + t.L1 * t.G ≤ C := by
    have hh := mul_nonneg (by positivity : 0 ≤ t.L0 + t.L1 * t.G + t.L1 * t.ε)
      (mul_nonneg h1 hR.le)
    dsimp [C, curvature]
    nlinarith [mul_nonneg h1 hε.le]
  have hgap : ⟪F p - F s, p - s⟫ ≤ t.ε * t.R := by
    have hh := GapNoiseStageDrift.regularized_root_gap c F p s hp hs
      (regularization_pos t hR hε _).le hroot hsolution
    exact hh.trans ((mul_le_mul_of_nonneg_right hbias (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hps hε.le))
  have hh := GapNoiseStageDrift.initial_gap_local c hF p s (by dsimp [c]; positivity)
    hR hε.le hdR hxp hps hFs hgap (by change t.L1 * d ≤ 1 / 2; linarith)
    hrootSlope (by change 4 * (t.L0 + t.L1 * t.G) ≤ 32 * C; nlinarith)
  change ⟪F x - F s, x - s⟫ ≤ t.ε * t.R + 3 * (32 * C) * t.R * d +
    t.ε * (1 + 2 * t.L1 * t.R) * d at hh
  have ht := mul_le_mul_of_nonneg_left hCd (by positivity : 0 ≤ 96 * t.R)
  have hb := mul_le_mul_of_nonneg_left hbd (by positivity : 0 ≤ 2 * t.ε * t.R)
  have he := mul_le_mul_of_nonneg_left hdR hε.le
  nlinarith [mul_pos hε hR]

lemma refinedGood_final_gap [FiniteDimensional ℝ E] {X : Set E} {P F : E → E}
    (hP : Proj X P) (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (hs : s ∈ X) (hsolution : Normal X s (-F s)) (hFs : ‖F s‖ ≤ t.G)
    (anchor x : E) (hg : GapNoiseOuter.RefinedGood hP t hF hR hε hx0 s (stageCount t, anchor, x)) :
    ⟪F x - F s, x - s⟫ ≤ 3 * t.ε * t.R := by
  let j := stageCount t - 1
  let p := analysisRoot hP t hF hR hε hx0 j anchor
  have hmin : min (stageCount t) (stageCount t - 1) = j := Nat.min_eq_right (by omega)
  have hp := analysisRoot_spec hP t hF hR hε hx0 j anchor
  have hclose := hg.1.2.1
  simp only [hmin, lt_self_iff_false, ite_false] at hclose
  have hps := GapNoiseOuter.refinedGood_root_distance hP t hF hR hε hx0 (stageCount t, anchor, x) hg
  simp only [hmin] at hps
  have hb := stageGood_bounds hP t hF hR hε hx0 hs hsolution hFs (stageCount t, anchor, x) hg.1
  simp only [hmin] at hb
  apply final_gap_bound t hF hR hε anchor x p s hp.1 hs hp.2 hsolution
  · rw [norm_sub_rev]
    exact hclose.trans (by have := radius_pos t hR j; linarith)
  · exact hps
  · exact hFs
  · exact hb.2
  · exact hb.1.trans (by linarith)

lemma finalBatch_variance (t : LongTails.Algorithms.GapNoisePastExtragradient.Tuning)
    (hε : 0 < t.ε) :
    (t.σ ^ 2 + 3 * t.v * t.ε * t.R) /
      (LongTails.Algorithms.GapNoisePastExtragradient.finalBatch t : ℝ) ≤ 3 * t.ε ^ 2 / 2 ^ 60 := by
  have hn := GapNoiseTuning.finalBatch_pos t
  have hn' : 0 < (LongTails.Algorithms.GapNoisePastExtragradient.finalBatch t : ℝ) := Nat.cast_pos.mpr hn
  have hceil : 2 ^ 60 * (t.σ ^ 2 / t.ε ^ 2 + t.v * t.R / t.ε) ≤
      (LongTails.Algorithms.GapNoisePastExtragradient.finalBatch t : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right _ _))
  have hh := mul_le_mul_of_nonneg_right hceil (sq_nonneg t.ε)
  have he : 2 ^ 60 * (t.σ ^ 2 / t.ε ^ 2 + t.v * t.R / t.ε) * t.ε ^ 2 =
      2 ^ 60 * (t.σ ^ 2 + t.v * t.R * t.ε) := by field_simp
  rw [he] at hh
  rw [div_le_iff₀ hn']
  nlinarith [sq_nonneg t.σ]

open LongTails.Algorithms.GapNoisePastExtragradient in
lemma finalBlockOutput_correct [FiniteDimensional ℝ E] {Ω : Type} {X : Set E} {P F : E → E}
    (hP : Proj X P) (t : LongTails.Algorithms.GapNoisePastExtragradient.Tuning)
    (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (hs : s ∈ X) (hsolution : Normal X s (-F s)) (hFs : ‖F s‖ ≤ t.G)
    (anchor x : E) (hg : StageGood hP (geometry t) hF hR hε hx0 s (stages t, anchor, x))
    (g : E → Ω → E) (ξ : Fin (finalCalls t) → Ω)
    (he : ‖finalBlockEstimate t x g ξ - F x‖ ≤ t.ε / 32) :
    finalBlockOutput P t anchor x g ξ ∈ X ∧
      ∃ η, Normal X (finalBlockOutput P t anchor x g ξ) η ∧
        ‖F (finalBlockOutput P t anchor x g ξ) + η‖ ≤ t.ε := by
  have hmin : min (stageCount (geometry t)) (stageCount (geometry t) - 1) =
      stageCount (geometry t) - 1 := Nat.min_eq_right (by omega)
  have hb := stageGood_bounds hP (geometry t) hF hR hε hx0 hs hsolution hFs (stages t, anchor, x) hg
  simp only [stages, hmin] at hb
  have hp := analysisRoot_spec hP (geometry t) hF hR hε hx0 (stageCount (geometry t) - 1) anchor
  have hc := hg.2.1
  simp only [stages, hmin, lt_self_iff_false, ite_false] at hc
  have hh := tuned_residual_certificate hP (geometry t) hF hR ((norm_nonneg _).trans hFs) hε
    _ anchor x (finalBlockEstimate t x g ξ - F x) hp.1 hp.2 hb.2
    (by simpa only [norm_sub_rev] using hc) he
    (by have hε' : 0 < (geometry t).ε := hε; linarith [hb.1])
  have heq : F x + (finalBlockEstimate t x g ξ - F x) = finalBlockEstimate t x g ξ := by abel
  simpa only [heq, finalBlockOutput, residualOutput, stages,
    show (geometry t).ε = t.ε from rfl] using hh

variable {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

open LongTails.Algorithms.GapNoisePastExtragradient in
lemma sampledFinalEstimate_confidence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : LongTails.Algorithms.GapNoisePastExtragradient.Tuning) (hε : 0 < t.ε) (hv : 0 ≤ t.v)
    {X : Set E} {F : E → E} {g : E → Ω → E} (s x : E)
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hx : x ∈ X) (hgap : ⟪F x - F s, x - s⟫ ≤ 3 * t.ε * t.R) :
    (Measure.pi fun _ : Fin (outerGroups t + 1) => Measure.pi fun _ : Fin (finalBatch t) => μ)
      {ξ | t.ε / 32 < ‖sampledFinalEstimate t x g ξ - F x‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (outerGroups t + 1)) := by
  let average : (Fin (finalBatch t) → Ω) → E := fun ξ =>
    (1 / (finalBatch t : ℝ)) • ∑ j, g x (ξ j)
  have hgm : Measurable (g x) := ho.measurable.comp measurable_prodMk_left
  have hm : Measurable average := by dsimp [average]; fun_prop
  have hn := GapNoiseTuning.finalBatch_pos t
  have hn' : 0 < (finalBatch t : ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨hi, he⟩ := RobustGradient.finite_mean_variance hgm (ho.integrable x hx) (F x)
    (ho.variance_integrable x hx) (ho.unbiased x hx) (finalBatch t) hn
  have hvar : (∫ ω, ‖g x ω - F x‖ ^ 2 ∂μ) ≤ t.σ ^ 2 + 3 * t.v * t.ε * t.R := by
    have hh := ho.variance x hx
    have hb := mul_le_mul_of_nonneg_left hgap hv
    nlinarith
  have hmean : (∫ ξ, ‖average ξ - F x‖ ^ 2 ∂Measure.pi (fun _ : Fin (finalBatch t) => μ)) ≤
      3 * t.ε ^ 2 / 2 ^ 60 := by
    dsimp [average]
    rw [he]
    exact (div_le_div_of_nonneg_right hvar hn'.le).trans (finalBatch_variance t hε)
  have hr : 0 < t.ε / 192 := by positivity
  have ht := RobustGradient.norm_tail_le_second_moment hi hr hmean
  have hb : (Measure.pi fun _ : Fin (finalBatch t) => μ).real
      {ξ | t.ε / 192 < ‖average ξ - F x‖} ≤ 1 / 256 := by
    apply ht.trans
    rw [div_le_iff₀ (sq_pos_of_pos hr)]
    nlinarith [sq_pos_of_pos hε]
  have hh := MultiplicativeRobustEstimator.medoid_failure_probability hm (F x) hr.le hb (outerGroups t)
  simpa only [sampledFinalEstimate, average, show 6 * (t.ε / 192) = t.ε / 32 by ring] using hh

open LongTails.Algorithms.GapNoisePastExtragradient in
lemma finalBlockEstimate_confidence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : LongTails.Algorithms.GapNoisePastExtragradient.Tuning) (hε : 0 < t.ε) (hv : 0 ≤ t.v)
    {X : Set E} {F : E → E} {g : E → Ω → E} (s x : E)
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hx : x ∈ X) (hgap : ⟪F x - F s, x - s⟫ ≤ 3 * t.ε * t.R) :
    (Measure.pi fun _ : Fin (finalCalls t) => μ)
      {ξ | t.ε / 32 < ‖finalBlockEstimate t x g ξ - F x‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (outerGroups t + 1)) := by
  have hm : Measurable (sampledFinalEstimate t x g) :=
    GapNoiseSampling.measurable_sampledFinalEstimate_of ho.measurable t measurable_const measurable_id
  have hset : MeasurableSet {ξ | t.ε / 32 < ‖sampledFinalEstimate t x g ξ - F x‖} :=
    measurableSet_lt measurable_const (hm.sub measurable_const).norm
  have he := (GapNoiseSampling.finalSamples_preserving μ t).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin (finalCalls t) => μ) (finalSamples t ⁻¹'
    {ξ | t.ε / 32 < ‖sampledFinalEstimate t x g ξ - F x‖}) ≤ _
  rw [he]
  exact sampledFinalEstimate_confidence μ t hε hv s x ho hx hgap

end LongTails.Proofs.GapNoiseFinal
