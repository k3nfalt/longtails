import LongTails.Algorithms.ProjectedClippedExtragradient
import LongTails.Proofs.ClippedExtragradientBlocks
import LongTails.Proofs.ProjectedClippedStage
import LongTails.Proofs.RobustEstimatorMoments
import LongTails.Setups.StochasticGeneralizedMonotone

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.ProjectedClippedExtragradient

lemma sampleIndex_injective (m : ℕ) : Function.Injective (sampleIndex m) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg Fin.val hij
  dsimp [sampleIndex] at he
  split_ifs at he <;> omega

variable {Ω : Type*} [MeasurableSpace Ω]

lemma stripSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) :
    MeasurePreserving (fun ξ : Fin ((1 + m + 1) + m) → Ω => fun i => ξ (sampleIndex m i))
      (Measure.pi fun _ : Fin ((1 + m + 1) + m) => P)
      (Measure.pi fun _ : Fin (m + m) => P) := by
  have hi := (iIndepFun_pi (μ := fun _ : Fin ((1 + m + 1) + m) => P)
    (X := fun _ (x : Ω) => x) (fun _ => measurable_id.aemeasurable)).precomp
      (sampleIndex_injective m)
  refine ⟨by fun_prop, ?_⟩
  have hh := hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply (sampleIndex m i)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : Fin ((1 + m + 1) + m) => P) _).map_eq] using hh

lemma stepSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) :
    MeasurePreserving (stepSamples (Ω := Ω) m)
      (Measure.pi fun _ : Fin ((1 + m + 1) + m) => P)
      ((Measure.pi (fun _ : Fin m => P)).prod (Measure.pi (fun _ : Fin m => P))) :=
  (ClippedExtragradient.splitBatches_preserving P m).comp (stripSamples_preserving P m)

lemma trialSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (m n : ℕ) :
    MeasurePreserving (trialSamples (Ω := Ω) m n)
      (Measure.pi fun _ : Fin (((1 + m + 1) + m) * n) => P)
      (Measure.pi fun _ : Fin n =>
        (Measure.pi (fun _ : Fin m => P)).prod (Measure.pi (fun _ : Fin m => P))) :=
  (measurePreserving_pi _ _ (fun _ : Fin n => stepSamples_preserving P m)).comp
    (ClippedExtragradient.groupSamples_preserving P ((1 + m + 1) + m) n)

lemma stageSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (t : Tuning) (s : ℕ) :
    MeasurePreserving (stageSamples (Ω := Ω) t s)
      (Measure.pi fun _ : Fin (stageCalls t s) => P)
      (Measure.pi fun _ : Fin (repetitions t) => Measure.pi fun _ : Fin (innerSteps t s) =>
        (Measure.pi (fun _ : Fin (batchSize t s) => P)).prod
          (Measure.pi (fun _ : Fin (batchSize t s) => P))) :=
  (measurePreserving_pi _ _ (fun _ : Fin (repetitions t) =>
    trialSamples_preserving P (batchSize t s) (innerSteps t s))).comp
      (ClippedExtragradient.groupSamples_preserving P
        (((1 + batchSize t s + 1) + batchSize t s) * innerSteps t s) (repetitions t))

lemma finalSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (t : Tuning) :
    MeasurePreserving (finalSamples (Ω := Ω) t)
      (Measure.pi fun _ : Fin (finalCalls t) => P)
      (Measure.pi fun _ : Fin (repetitions t) => Measure.pi fun _ : Fin (finalBatchSize t) => P) := by
  have hh := RobustGradient.stream_groups_preserving P (repetitions t) (finalBatchSize t)
  have hm : Measurable (finalSamples (Ω := Ω) t) := by unfold finalSamples; fun_prop
  refine ⟨hm, ?_⟩
  rw [← (StochasticGeneralized.prefix_preserving P (finalCalls t)).map_eq,
    Measure.map_map hm (by fun_prop)]
  convert hh.map_eq using 1
  congr 1
  funext ξ j i
  simp only [Function.comp_def, finalSamples, Nat.mul_comm]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option maxHeartbeats 1200000 in
lemma measurable_trial_joint {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × (Fin (innerSteps t s) →
        (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) =>
      trialOutput P (innerSteps t s) (batchSize t s) t.L1 (localScale t s)
        (radius t s) (regularization t s) w.1.1 w.1.2 g w.2) := by
  have ha : Measurable (fun w : (E × E) × E ×
      ((Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) =>
      batchStep P (batchSize t s) t.L1 (localScale t s) (radius t s)
        (regularization t s) w.1.1 w.1.2 g w.2.1 w.2.2) :=
    measurable_batchStep_of hP hg _ _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact (ClippedExtragradient.measurable_iterateSamples_parameter
    (advance := fun a : E × E => batchStep P (batchSize t s) t.L1 (localScale t s)
      (radius t s) (regularization t s) a.1 a.2 g) ha (innerSteps t s)).comp
    (measurable_fst.prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

set_option maxHeartbeats 1200000 in
lemma measurable_confidence_joint {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × (Fin (repetitions t) → Fin (innerSteps t s) →
        (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) =>
      confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t) t.L1 (localScale t s)
        (radius t s) (regularization t s) w.1.1 w.1.2 g w.2) := by
  have ht := ClippedExtragradient.measurable_finite_replies (measurable_trial_joint hP hg t s) (repetitions t)
  have hc : Measurable (fun w : (E × E) × (Fin (repetitions t) → Fin (innerSteps t s) →
      (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) => w.1.2) := by fun_prop
  have hshift := ht.sub (Measurable.of_eval (fun _ : Fin (repetitions t) => hc))
  have hpilot := (RobustGradient.measurable_pilotCenter (repetitions t)).comp
    ((measurable_const (a := radius t s)).prodMk hshift)
  change Measurable (fun w : (E × E) × (Fin (repetitions t) → Fin (innerSteps t s) →
      (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) => w.1.2 + clip (2 * radius t s)
    (RobustGradient.pilotCenter (radius t s)
      (fun i => trialOutput P (innerSteps t s) (batchSize t s) t.L1 (localScale t s)
        (radius t s) (regularization t s) w.1.1 w.1.2 g (w.2 i) - w.1.2)))
  exact hc.add ((measurable_clip _).comp hpilot)

lemma measurable_blockOutput_joint {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × (Fin (stageCalls t s) → Ω) =>
      blockOutput P t s w.1.1 w.1.2 g w.2) := by
  have hs : Measurable (stageSamples (Ω := Ω) t s) := by
    unfold stageSamples trialSamples stepSamples ClippedExtragradient.splitBatches
      ClippedExtragradient.groupSamples
    fun_prop
  exact (measurable_confidence_joint hP hg t s).comp (measurable_fst.prodMk (hs.comp measurable_snd))

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma blockOutput_mem {X : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj X P)
    (hX : Convex ℝ X) (t : Tuning) (hR : 0 < t.R) (s : ℕ)
    (anchor center : E) (hc : center ∈ X) (g : E → Ω → E)
    (ξ : Fin (stageCalls t s) → Ω) : blockOutput P t s anchor center g ξ ∈ X := by
  apply aggregate_mem hX (radius_pos t hR s).le hc
  intro j
  exact trial_mem hP hX g _ _ _ _ _ _ (radius_pos t hR s).le anchor center hc _

lemma measurable_finalEstimate_joint {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : Tuning) :
    Measurable (fun w : E × (Fin (finalCalls t) → Ω) => finalEstimate t w.1 g w.2) := by
  have hm : Measurable (fun w : E × (Fin (finalCalls t) → Ω) =>
      fun j : Fin (repetitions t) => (1 / (finalBatchSize t : ℝ)) •
        ∑ i : Fin (finalBatchSize t), g w.1 (finalSamples t w.2 j i)) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i hi
    exact hg.comp (measurable_fst.prodMk (by fun_prop))
  exact (RobustGradient.measurable_pilotCenter (repetitions t)).comp
    ((measurable_const (a := t.ε / 16)).prodMk hm)

lemma measurable_finalBlock_joint {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) :
    Measurable (fun w : (E × E) × (Fin (finalCalls t) → Ω) => finalBlock P t w.1.1 w.1.2 g w.2) := by
  have he : Measurable (fun w : (E × E) × (Fin (finalCalls t) → Ω) =>
      finalEstimate t w.1.2 g w.2) := (measurable_finalEstimate_joint hg t).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  unfold finalBlock residualOutput ClippedExtragradient.regularizedReply
  exact hP.comp ((measurable_snd.comp measurable_fst).sub
    ((he.add (((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)).const_smul _)).const_smul _))

lemma measurable_phaseReply {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (phaseReply P t g n)) := by
  have hs := ClippedExtragradient.measurable_guarded_block (Ω := Ω) (stageCalls t)
    (fun s (a : E × E) ξ => blockOutput P t s a.1 a.2 g ξ) Prod.snd measurable_snd
    (measurable_blockOutput_joint hP hg t) n
  have hf : Measurable (fun w : ProcessState E × (Fin n → Ω) =>
      if hn : n = finalCalls t then finalBlock P t w.1.2.1 w.1.2.2 g
        (fun i => w.2 (Fin.cast hn.symm i)) else w.1.2.2) := by
    by_cases hn : n = finalCalls t
    · subst n
      simpa only [dite_true, Fin.cast_refl, id_eq, Function.comp_def] using
        (measurable_finalBlock_joint hP hg t).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    · simp only [hn, dite_false]
      fun_prop
  exact hs.ite (measurableSet_lt (by fun_prop) measurable_const) hf

lemma measurable_phaseNext {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (phaseNext P t g n)) := by
  classical
  have hw := measurable_phaseReply hP hg t n
  have ha : Measurable (fun w : ProcessState E × (Fin n → Ω) => w.1.2.1) := by fun_prop
  have hx : Measurable (fun w : ProcessState E × (Fin n → Ω) =>
      if w.1.1 + 1 < stageCount t then (1 / 2 : ℝ) • (w.1.2.1 + phaseReply P t g n w.1 w.2)
      else w.1.2.1) := ((ha.add hw).const_smul (1 / 2 : ℝ)).ite
    (measurableSet_lt (show Measurable (fun w : ProcessState E × (Fin n → Ω) => w.1.1 + 1) by fun_prop)
      (measurable_const (a := stageCount t))) ha
  exact (by fun_prop : Measurable (fun w : ProcessState E × (Fin n → Ω) => w.1.1 + 1)).prodMk
    (hx.prodMk hw)

variable [CompleteSpace E]

lemma blockOutput_confidence {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : ConstrainedMonotone.Proj X P) (hX : Convex ℝ X)
    {g : E → Ω → E} (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator Q F g t.σ)
    (s : ℕ) (anchor center p : E) (hp : p ∈ X) (hc : center ∈ X)
    (hpc : ‖p - center‖ ≤ radius t s)
    (hnp : ConstrainedMonotone.Normal X p (-(F p + regularization t s • (p - anchor))))
    (hM : ‖F p‖ ≤ rootBound t) (hbias : regularization t s * ‖p - anchor‖ ≤ t.ε) :
    (Measure.pi fun _ : Fin (stageCalls t s) => Q)
      {ξ | radius t s / 2 < ‖blockOutput P t s anchor center g ξ - p‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ repetitions t) := by
  have hm : Measurable (confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t)
      t.L1 (localScale t s) (radius t s) (regularization t s) anchor center g) := by
    change Measurable ((fun w : (E × E) × (Fin (repetitions t) → Fin (innerSteps t s) →
      (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) =>
      confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t) t.L1 (localScale t s)
        (radius t s) (regularization t s) w.1.1 w.1.2 g w.2) ∘ fun ξ => ((anchor, center), ξ))
    exact (measurable_confidence_joint hP.lipschitz.continuous.measurable hg.measurable t s).comp
      measurable_prodMk_left
  have hset : MeasurableSet {ξ | radius t s / 2 < ‖confidenceOutput P (innerSteps t s)
      (batchSize t s) (repetitions t) t.L1 (localScale t s) (radius t s)
      (regularization t s) anchor center g ξ - p‖} :=
    measurableSet_lt measurable_const (hm.sub measurable_const).norm
  have he := (stageSamples_preserving Q t s).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin (stageCalls t s) => Q) (stageSamples t s ⁻¹'
    {ξ | radius t s / 2 < ‖confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t)
      t.L1 (localScale t s) (radius t s) (regularization t s) anchor center g ξ - p‖}) ≤ _
  rw [he]
  exact tuned_stage_confidence hP hX t hF hR hG hε hg.measurable hg.integrable hg.unbiased
    hg.variance_integrable hg.variance s anchor center p hp hc hpc hnp hM hbias

lemma finalEstimate_confidence {Q : Measure Ω} [IsProbabilityMeasure Q] {g : E → Ω → E}
    {F : E → E} (t : Tuning) (hε : 0 < t.ε)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator Q F g t.σ) (x : E) :
    (Measure.pi fun _ : Fin (finalCalls t) => Q)
      {ξ | t.ε / 32 < ‖finalEstimate t x g ξ - F x‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ repetitions t) := by
  let est := fun ξ : Fin (repetitions t) → Fin (finalBatchSize t) → Ω =>
    RobustGradient.pilotCenter (t.ε / 16) (fun j => (1 / (finalBatchSize t : ℝ)) •
      ∑ i, g x (ξ j i))
  have hmeans : Measurable (fun ξ : Fin (repetitions t) → Fin (finalBatchSize t) → Ω =>
      fun j => (1 / (finalBatchSize t : ℝ)) • ∑ i, g x (ξ j i)) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i hi
    exact hg.measurable.comp (measurable_const.prodMk (by fun_prop))
  have hm : Measurable est := (RobustGradient.measurable_pilotCenter (repetitions t)).comp
    ((measurable_const (a := t.ε / 16)).prodMk hmeans)
  have hset : MeasurableSet {ξ | t.ε / 32 < ‖est ξ - F x‖} :=
    measurableSet_lt measurable_const (hm.sub measurable_const).norm
  have he := (finalSamples_preserving Q t).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin (finalCalls t) => Q)
    (finalSamples t ⁻¹' {ξ | t.ε / 32 < ‖est ξ - F x‖}) ≤ _
  rw [he]
  have hh := RobustGradient.pilot_means_failure_probability
    (hg.measurable.comp measurable_prodMk_left) (hg.integrable x) (F x) (hg.unbiased x)
    (hg.variance_integrable x) (hg.variance x) (by positivity : 0 < t.ε / 16)
    (repetitions t) (finalBatchSize t) (finalBatchSize_pos t) (finalBatchSize_tail t hε)
  simpa only [est, Function.comp_apply, Function.uncurry_apply_pair, div_div,
    show (16 : ℝ) * 2 = 32 by norm_num] using hh

end OracleTemplate.ProjectedClippedExtragradient
