import LongTails.Proofs.StochasticEqualityConfidence

namespace LongTails.Proofs.StochasticEqualityAmplification

open MeasureTheory OracleTemplate
open scoped ENNReal
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.StochasticEquality
open LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.StochasticEqualityExecution
open LongTails.Proofs.StochasticEqualitySampling
open LongTails.Proofs.StochasticEqualityConfidence
open LongTails.Proofs.StochasticEqualityMoments

noncomputable def rejectIndicator {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (index : Fin cfg.steps) (offset : ℕ) : ℝ := by
  classical
  exact if QueryPlan.sampledEval g (fun j => ξ (j / 2)) (trialPlan p cfg index) (2 * offset) = none then 1 else 0

lemma rejectIndicator_eq_one {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (index : Fin cfg.steps) (offset : ℕ) :
    rejectIndicator p cfg g ξ index offset = 1 ↔
      QueryPlan.sampledEval g (fun j => ξ (j / 2)) (trialPlan p cfg index) (2 * offset) = none := by
  classical
  unfold rejectIndicator
  split_ifs <;> simp_all

lemma measurable_rejectIndicator {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (index : Fin cfg.steps) (offset : ℕ) :
    Measurable (fun ξ => rejectIndicator p cfg g ξ index offset) := by
  classical
  have he (ξ : ℕ → Ω) := sampled_trial p cfg g ξ index offset
  have hm := measurableSet_validate_none p cfg
    (fun ξ => trialPoint p cfg g ξ index offset) (fun ξ => trialEstimate p cfg g ξ index offset)
    (measurable_trialEstimate p cfg g hg index offset)
  have hs : MeasurableSet {ξ : ℕ → Ω | QueryPlan.sampledEval g (fun j => ξ (j / 2))
      (trialPlan p cfg index) (2 * offset) = none} := by simpa only [he] using hm
  exact measurable_const.ite hs measurable_const

lemma trial_rejection_factor {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g)) :
    ∃ F : Fin cfg.steps → (Fin (trialSamples cfg) → Ω) → ℝ,
      (∀ i, Measurable (F i)) ∧
        ∀ i ξ, rejectIndicator p cfg g ξ i 0 = F i (fun j => ξ j.val) := by
  have hd (i : Fin cfg.steps) (ξ ζ : ℕ → Ω)
      (h : ∀ j < trialSamples cfg, ξ j = ζ j) :
      rejectIndicator p cfg g ξ i 0 = rejectIndicator p cfg g ζ i 0 := by
    have hh := paired_prefix_congr g ξ ζ (castPlan (trial_calls cfg) (trialPlan p cfg i)) 0
      (by simpa only [Nat.zero_add] using h)
    simp only [sampled_cast, Nat.mul_zero] at hh
    simp only [rejectIndicator, Nat.mul_zero, hh]
  have hex (i : Fin cfg.steps) := SymmetricThirdOrderSampling.measurable_prefix_factor P (trialSamples cfg)
    (fun ξ => rejectIndicator p cfg g ξ i 0) (measurable_rejectIndicator p cfg g hg i 0) (hd i)
  choose F hF hEq using hex
  exact ⟨F, hF, hEq⟩

lemma block_rejection_probability {Ω : Type*} [MeasurableSpace Ω] (p : Public) (cfg : Config)
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure (Fin cfg.steps))
    (g : Point p.d → Ω → Reply p) (F : Fin cfg.steps → (Fin (trialSamples cfg) → Ω) → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hEq : ∀ i ξ, rejectIndicator p cfg g ξ i 0 = F i (fun j => ξ j.val))
    (δ : ℝ≥0∞)
    (hsingle : (ρ.prod (Measure.infinitePi fun _ : ℕ => P))
      {z | QueryPlan.sampledEval g (fun j => z.2 (j / 2)) (trialPlan p cfg z.1) 0 = none} ≤ δ) :
    (ρ.prod (Measure.pi fun _ : Fin (trialSamples cfg) => P)) {z | F z.1 z.2 = 1} ≤ δ := by
  have hm : Measurable (fun z : Fin cfg.steps × (Fin (trialSamples cfg) → Ω) => F z.1 z.2) :=
    measurable_from_prod_countable_right hF
  have hA := measurableSet_eq_fun hm (measurable_const (a := (1 : ℝ)))
  have hmp := (MeasurePreserving.id ρ).prod (StochasticGeneralized.prefix_preserving P (trialSamples cfg))
  rw [← hmp.measure_preimage hA.nullMeasurableSet]
  convert hsingle using 1
  congr 1
  ext z
  change (F z.1 (fun j => z.2 j.val) = 1) ↔
    QueryPlan.sampledEval g (fun j => z.2 (j / 2)) (trialPlan p cfg z.1) 0 = none
  rw [← hEq]
  exact rejectIndicator_eq_one p cfg g z.2 z.1 0

lemma all_trials_rejected {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g)) (δ : ℝ≥0∞)
    (hsingle : ((PMF.uniformOfFintype (Fin cfg.steps)).toMeasure.prod (Measure.infinitePi fun _ : ℕ => P))
      {z | QueryPlan.sampledEval g (fun j => z.2 (j / 2)) (trialPlan p cfg z.1) 0 = none} ≤ δ) :
    (((seedLaw cfg : Measure (Seed cfg))).prod Q)
      {z | ∀ i : Fin cfg.trials, QueryPlan.sampledEval g (fun j => ξ (j / 2) z.2)
        (trialPlan p cfg (z.1 i)) (trialCalls cfg * i.val) = none} ≤ δ ^ (cfg.trials : ℕ) := by
  obtain ⟨F, hF, hEq⟩ := trial_rejection_factor p cfg P g hg
  let ρ := (PMF.uniformOfFintype (Fin cfg.steps)).toMeasure
  let B : Set (Fin cfg.steps × (Fin (trialSamples cfg) → Ω)) := {z | F z.1 z.2 = 1}
  let C : Set (Fin cfg.trials → (Fin cfg.steps × (Fin (trialSamples cfg) → Ω))) := Set.univ.pi (fun _ => B)
  let φ := fun z : Seed cfg × Ξ => fun i : Fin cfg.trials =>
    (z.1 i, fun j : Fin (trialSamples cfg) => ξ (trialSamples cfg * i.val + j.val) z.2)
  have hm : Measurable (fun z : Fin cfg.steps × (Fin (trialSamples cfg) → Ω) => F z.1 z.2) :=
    measurable_from_prod_countable_right hF
  have hB : MeasurableSet B := measurableSet_eq_fun hm (measurable_const (a := (1 : ℝ)))
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _ => hB)
  have hmap : MeasurePreserving φ ((seedLaw cfg : Measure (Seed cfg)).prod Q)
      (Measure.pi fun _ : Fin cfg.trials => ρ.prod (Measure.pi fun _ : Fin (trialSamples cfg) => P)) :=
    independent_seed_blocks h cfg.trials (trialSamples cfg) cfg.steps ρ
  have hpre : φ ⁻¹' C = {z | ∀ i : Fin cfg.trials,
      QueryPlan.sampledEval g (fun j => ξ (j / 2) z.2) (trialPlan p cfg (z.1 i)) (trialCalls cfg * i.val) = none} := by
    ext z
    simp only [Set.mem_preimage, C, Set.mem_univ_pi, φ, B, Set.mem_ofPred_eq]
    apply forall_congr'
    intro i
    rw [← hEq (z.1 i) (fun j => ξ (trialSamples cfg * i.val + j) z.2), rejectIndicator_eq_one]
    have hs := paired_sampled_shift g (fun j => ξ j z.2) (trialPlan p cfg (z.1 i)) (trialSamples cfg * i.val)
    have hcall : trialCalls cfg * i.val = 2 * (trialSamples cfg * i.val) := by
      rw [trial_calls]
      ring
    rw [hcall, hs, Nat.mul_zero]
  have hb := block_rejection_probability p cfg P ρ g F hF hEq δ hsingle
  calc
    _ = ((seedLaw cfg : Measure (Seed cfg)).prod Q) (φ ⁻¹' C) := by rw [hpre]
    _ = (Measure.pi fun _ : Fin cfg.trials => ρ.prod (Measure.pi fun _ : Fin (trialSamples cfg) => P)) C :=
      hmap.measure_preimage hC.nullMeasurableSet
    _ = ((ρ.prod (Measure.pi fun _ : Fin (trialSamples cfg) => P)) B) ^ (cfg.trials : ℕ) := by
      simp only [C, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ δ ^ (cfg.trials : ℕ) := by gcongr

lemma all_validation_failure {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (cfg : Config) {ξ : ℕ → Ξ → Ω} {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : IID ξ P Q)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) (hi : ∀ y, Integrable (g y) P)
    (hm : ∀ y, ∫ w, g y w ∂P = u y)
    (h2 : ∀ y, Integrable (fun w => ‖pack p (g y w) -
      pack p (u y)‖ ^ 2) P)
    (hv : ∀ y, (∫ w, ‖pack p (g y w) -
      pack p (u y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (ht : 0 < cfg.validationTolerance)
    (hsize : p.σ ^ 2 / (cfg.validationBatch : ℝ) ≤ cfg.validationTolerance ^ 2 / 144) :
    ((seedLaw cfg : Measure (Seed cfg)).prod Q)
      {z | ∃ i : Fin cfg.trials, ¬ replyAccurate p cfg.validationTolerance
        (u (trialPoint p cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val)))
        (trialEstimate p cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val))} ≤
      3 * (cfg.trials : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ)) := by
  let ρ := (PMF.uniformOfFintype (Fin cfg.steps)).toMeasure
  let A := fun i : Fin cfg.trials => {z : Fin cfg.steps × Ξ | ¬ replyAccurate p cfg.validationTolerance
    (u (trialPoint p cfg g (fun j => ξ j z.2) z.1 (trialSamples cfg * i.val)))
    (trialEstimate p cfg g (fun j => ξ j z.2) z.1 (trialSamples cfg * i.val))}
  let B := fun i : Fin cfg.trials => (fun z : Seed cfg × Ξ => (z.1 i, z.2)) ⁻¹' A i
  have hstream : Measurable (fun z j => ξ j z) := Measurable.of_eval h.measurable
  have hA (i : Fin cfg.trials) : MeasurableSet (A i) := by
    have hp : Measurable (fun z : Fin cfg.steps × Ξ => trialPoint p cfg g (fun j => ξ j z.2) z.1 (trialSamples cfg * i.val)) :=
      measurable_from_prod_countable_right fun k =>
        (measurable_trialPoint p cfg g hg k (trialSamples cfg * i.val)).comp hstream
    have hv' : Measurable (fun z : Fin cfg.steps × Ξ => trialEstimate p cfg g (fun j => ξ j z.2) z.1 (trialSamples cfg * i.val)) :=
      measurable_from_prod_countable_right fun k =>
        (measurable_trialEstimate p cfg g hg k (trialSamples cfg * i.val)).comp hstream
    exact (measurableSet_replyAccurate p cfg.validationTolerance
      (fun z : Fin cfg.steps × Ξ => u (trialPoint p cfg g (fun j => ξ j z.2) z.1 (trialSamples cfg * i.val)))
      (fun z : Fin cfg.steps × Ξ => trialEstimate p cfg g (fun j => ξ j z.2) z.1 (trialSamples cfg * i.val))
      (hu.comp hp) hv').compl
  have hB (i : Fin cfg.trials) : ((seedLaw cfg : Measure (Seed cfg)).prod Q) (B i) ≤
      3 * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ)) := by
    have hmp := (measurePreserving_eval (fun _ : Fin cfg.trials => ρ) i).prod (MeasurePreserving.id Q)
    have he := hmp.measure_preimage (hA i).nullMeasurableSet
    have hh := trial_estimate_confidence_product p cfg h g hg u hu hi hm h2 hv ht hsize ρ (trialSamples cfg * i.val)
    rw [← he] at hh
    exact hh
  have he : {z : Seed cfg × Ξ | ∃ i : Fin cfg.trials, ¬ replyAccurate p cfg.validationTolerance
      (u (trialPoint p cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val)))
      (trialEstimate p cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val))} = ⋃ i, B i := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, B, A, Set.mem_preimage]
  rw [he]
  calc
    _ ≤ ∑' i : Fin cfg.trials, ((seedLaw cfg : Measure (Seed cfg)).prod Q) (B i) := measure_iUnion_le _
    _ ≤ ∑' _ : Fin cfg.trials, 3 * ENNReal.ofReal ((1 / 2 : ℝ) ^ (cfg.validationGroups : ℕ)) := ENNReal.tsum_le_tsum hB
    _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

set_option maxHeartbeats 1000000 in
lemma admissible_all_trials_rejected {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] {ξ : ℕ → Ξ → Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure Q] (hsamples : IID ξ P Q) :
    let cfg := tuning p.toPublic
    ((seedLaw cfg : Measure (Seed cfg)).prod Q)
      {z | ∀ i : Fin cfg.trials, QueryPlan.sampledEval g (fun j => ξ (j / 2) z.2)
        (trialPlan p.toPublic cfg (z.1 i)) (trialCalls cfg * i.val) = none} ≤
      (ENNReal.ofReal (1 / 2 : ℝ)) ^ (cfg.trials : ℕ) := by
  apply all_trials_rejected p.toPublic (tuning p.toPublic) hsamples g hg (ENNReal.ofReal (1 / 2 : ℝ))
  simpa only [Nat.mul_zero] using trial_rejection_probability p hp I O hI P g hg hi hmean hnoise2 hnoise hdiff2 hdiff 0

lemma admissible_selected_sound {Ω : Type*} (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (g : Point p.d → Ω → Reply p.toPublic)
    (ξ : ℕ → Ω) (seed : Seed (tuning p.toPublic))
    (haccept : ¬ ∀ i : Fin (tuning p.toPublic).trials,
      QueryPlan.sampledEval g (fun j => ξ (j / 2))
        (trialPlan p.toPublic (tuning p.toPublic) (seed i))
        (trialCalls (tuning p.toPublic) * i.val) = none)
    (haccurate : ∀ i : Fin (tuning p.toPublic).trials,
      replyAccurate p.toPublic (tuning p.toPublic).validationTolerance
        (StochasticEqualityModel.truth I (trialPoint p.toPublic (tuning p.toPublic) g ξ
          (seed i) (trialSamples (tuning p.toPublic) * i.val)))
        (trialEstimate p.toPublic (tuning p.toPublic) g ξ
          (seed i) (trialSamples (tuning p.toPublic) * i.val))) :
    let y := QueryPlan.sampledEval g (fun j => ξ (j / 2))
      (plan p.toPublic (tuning p.toPublic) seed) 0
    ‖gradient I.f y.1 + (fderiv ℝ I.c y.1).adjoint y.2‖ ^ 2 + ‖I.c y.1‖ ^ 2 ≤ p.ε ^ 2 / 4 := by
  obtain ⟨i, hi⟩ := sampled_selected_trial p.toPublic (tuning p.toPublic) g
    (fun j => ξ (j / 2)) seed haccept
  have hcall : trialCalls (tuning p.toPublic) * i.val =
      2 * (trialSamples (tuning p.toPublic) * i.val) := by
    rw [trial_calls]
    ring
  rw [hcall, sampled_trial] at hi
  have ha := haccurate i
  exact StochasticEqualityValidation.admissible_validate_sound p hp I O hI _ _
    ha.1 ha.2.1 ha.2.2 _ hi

lemma trialPoint_displacement {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (index : Fin cfg.steps) (offset : ℕ)
    (hν : 0 < p.ν) (hL : 0 ≤ p.Lc) (hG : 0 ≤ cfg.gradientCap)
    (hM : 0 ≤ cfg.constraintCap) (hη : 0 ≤ cfg.step)
    (hRM : 0 ≤ cfg.restoreCap) (hRη : 0 ≤ cfg.restoreStep) :
    ‖trialPoint p cfg g ξ index offset - p.x0‖ ≤
      (cfg.restoreSteps : ℝ) * (cfg.restoreStep * p.Lc * cfg.restoreCap) +
      (cfg.steps : ℝ) * (cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap)) := by
  let x := restorationTrace p cfg g ξ offset cfg.restoreSteps
  have ht := training_path_bound p cfg g (fun i => ξ (i / 2)) index x
    (2 * trainingOffset cfg offset) hν hL hG hM hη
  have hr := restoration_path_bound p cfg g (fun i => ξ (i / 2)) (2 * offset) hL hRM hRη
  have hidx : (index : ℝ) ≤ (cfg.steps : ℝ) := by exact_mod_cast index.isLt.le
  have hm := mul_le_mul_of_nonneg_right hidx
    (show 0 ≤ cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap) by positivity)
  have he : trialPoint p cfg g ξ index offset - p.x0 =
      (trialPoint p cfg g ξ index offset - x) + (x - p.x0) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by
    change ‖trialPoint p cfg g ξ index offset - x‖ ≤ _ at ht
    change ‖x - p.x0‖ ≤ _ at hr
    linarith only [ht, hr, hm])

lemma output_path_bounds {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (seed : Seed cfg)
    (hν : 0 < p.ν) (hG : 0 ≤ cfg.gradientCap) {D : ℝ} (hD : 0 ≤ D)
    (hdist : ∀ i : Fin cfg.trials,
      ‖trialPoint p cfg g ξ (seed i) (trialSamples cfg * i.val) - p.x0‖ ≤ D) :
    let y := QueryPlan.sampledEval g (fun j => ξ (j / 2)) (plan p cfg seed) 0
    ‖y.1 - p.x0‖ ≤ D ∧ ‖y.2‖ ≤ 2 * cfg.gradientCap / p.ν := by
  let y := QueryPlan.sampledEval g (fun j => ξ (j / 2)) (plan p cfg seed) 0
  have hcases : y = (p.x0, 0) ∨ ∃ i : Fin cfg.trials,
      QueryPlan.sampledEval g (fun j => ξ (j / 2)) (trialPlan p cfg (seed i))
        (trialCalls cfg * i.val) = some y := by
    have hh := firstAccepted_mem_or_fallback p (p.x0, 0)
      (List.ofFn fun i : Fin cfg.trials => QueryPlan.sampledEval g (fun j => ξ (j / 2))
        (trialPlan p cfg (seed i)) (trialCalls cfg * i.val))
    simpa only [y, sampled_trials, Nat.zero_add, List.mem_ofFn] using hh
  change ‖y.1 - p.x0‖ ≤ D ∧ ‖y.2‖ ≤ _
  rcases hcases with hy | ⟨i, hi⟩
  · rw [hy]
    simp only [sub_self, norm_zero]
    exact ⟨hD, div_nonneg (mul_nonneg (by norm_num) hG) hν.le⟩
  · have hcall : trialCalls cfg * i.val = 2 * (trialSamples cfg * i.val) := by
      rw [trial_calls]
      ring
    rw [hcall, sampled_trial] at hi
    have hv := validate_properties p cfg hν hG _ _ y hi
    exact ⟨by rw [hv.1]; exact hdist i, hv.2⟩

lemma admissible_output_envelope {Ω : Type*} (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (g : Point p.d → Ω → Reply p.toPublic)
    (ξ : ℕ → Ω) (seed : Seed (tuning p.toPublic)) :
    let y := QueryPlan.sampledEval g (fun j => ξ (j / 2)) (plan p.toPublic (tuning p.toPublic) seed) 0
    ‖gradient I.f y.1 + (fderiv ℝ I.c y.1).adjoint y.2‖ ^ 2 + ‖I.c y.1‖ ^ 2 ≤
      10 ^ 33 * StochasticEqualityTuning.scale p.toPublic ^ 38 / p.ε ^ 4 := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  let D := 10 ^ 16 * S ^ 18 / p.ε ^ 2
  have hS := (StochasticEqualityTuning.scale_bounds p hp).1
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hS0 : 0 < S := by linarith only [hS1]
  have hν := hp.2.2.2.1
  have hLc := hp.2.2.2.2.2.1
  have hC0 := hp.2.2.2.2.2.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hgeo := StochasticEqualityTuning.tuning_geometry p hp
  have hrest := StochasticEqualityTuning.tuning_restoration_geometry p hp
  have hRM : 0 ≤ cfg.restoreCap := by change 0 ≤ p.C0 + 1; linarith only [hC0]
  have hd : ∀ i : Fin cfg.trials,
      ‖trialPoint p.toPublic cfg g ξ (seed i) (trialSamples cfg * i.val) - p.x0‖ ≤ D := by
    intro i
    exact (trialPoint_displacement p.toPublic cfg g ξ (seed i) (trialSamples cfg * i.val)
      hν hLc hgeo.2.1 hgeo.2.2.1 hgeo.1.le hRM hrest.1.le).trans
        (StochasticEqualityRestoration.tuning_path_distance p hp)
  have hout := output_path_bounds p.toPublic cfg g ξ seed hν hgeo.2.1
    (show 0 ≤ D by dsimp [D]; positivity) hd
  have hlam : 2 * cfg.gradientCap / p.ν ≤ 8000 * S ^ 7 := by
    have hinv := (StochasticEqualityTuning.scale_bounds p hp).2.2.2.2.2.2.1
    have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 8000 * S ^ 6 by positivity)
    change 2 * (4000 * S ^ 6) / p.ν ≤ _
    convert hh using 1 <;> ring
  have he := StochasticEqualityModel.admissible_point_envelope p hp I O hI _ _ hout.1 (hout.2.trans hlam)
  exact StochasticEqualityTuning.residual_envelope hS1 hε hε1 (norm_nonneg _) (norm_nonneg _) he.1 he.2

lemma measurable_sampled_output {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : Seed cfg × (ℕ → Ω) =>
      QueryPlan.sampledEval g (fun j => z.2 (j / 2)) (plan p cfg z.1) 0) := by
  apply measurable_from_prod_countable_right
  intro seed
  let values := List.ofFn fun i : Fin cfg.trials => fun ξ : ℕ → Ω =>
    QueryPlan.sampledEval g (fun j => ξ (j / 2)) (trialPlan p cfg (seed i)) (trialCalls cfg * i.val)
  have hv : ∀ v ∈ values, ∀ f : (ℕ → Ω) → Point p.d × Point p.m,
      Measurable f → Measurable (fun z => (v z).getD (f z)) := by
    intro v hv f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    have hcall : trialCalls cfg * i.val = 2 * (trialSamples cfg * i.val) := by
      rw [trial_calls]
      ring
    simp_rw [hcall, sampled_trial]
    exact measurable_validate_getD p cfg _ _ f
      (measurable_trialPoint p cfg g hg (seed i) _) (measurable_trialEstimate p cfg g hg (seed i) _) hf
  have hh := measurable_firstAccepted p values hv (fun _ => (p.x0, 0)) measurable_const
  simpa only [sampled_trials, Nat.zero_add, values, List.map_ofFn, Function.comp_def] using hh

lemma integral_two_failures {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : Measurable f)
    {A B : Set Z} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {M c δ : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hf0 : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (hgood : ∀ z, z ∉ A → z ∉ B → f z ≤ c)
    (hPA : μ A ≤ ENNReal.ofReal δ) (hPB : μ B ≤ ENNReal.ofReal δ) :
    Integrable f μ ∧ (∫ z, f z ∂μ) ≤ c + 2 * M * δ := by
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 z)] using hfM z)
  have hIA : Integrable (A.indicator (fun _ : Z => M)) μ := (integrable_const M).indicator hA
  have hIB : Integrable (B.indicator (fun _ : Z => M)) μ := (integrable_const M).indicator hB
  have hdom (z : Z) : f z ≤ c + A.indicator (fun _ : Z => M) z + B.indicator (fun _ : Z => M) z := by
    by_cases ha : z ∈ A <;> by_cases hb : z ∈ B
    · simp only [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      linarith only [hfM z, hM, hc]
    · simp only [Set.indicator_of_mem ha, Set.indicator_of_notMem hb, add_zero]
      linarith only [hfM z, hc]
    · simp only [Set.indicator_of_notMem ha, Set.indicator_of_mem hb, add_zero]
      linarith only [hfM z, hc]
    · simpa only [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb, add_zero] using hgood z ha hb
  have hh := integral_mono hi (((integrable_const c).add hIA).add hIB) hdom
  simp only [Pi.add_apply] at hh
  have hsum : Integrable (fun z => c + A.indicator (fun _ : Z => M) z) μ := (integrable_const c).add hIA
  rw [integral_add hsum hIB,
    integral_add (integrable_const c) hIA, integral_const, integral_indicator_const M hA,
    integral_indicator_const M hB] at hh
  have hpa : μ.real A ≤ δ := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hPA
  have hpb : μ.real B ≤ δ := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hPB
  have huniv : μ.real Set.univ = 1 := by simp [measureReal_def]
  simp only [huniv, smul_eq_mul] at hh
  refine ⟨hi, hh.trans ?_⟩
  nlinarith only [mul_le_mul_of_nonneg_right hpa hM, mul_le_mul_of_nonneg_right hpb hM]
lemma expected_output_of_tails {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (ξ : ℕ → Ξ → Ω) (hξ : Measurable (fun z j => ξ j z))
    (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (hPA : ((seedLaw (tuning p.toPublic) : Measure (Seed (tuning p.toPublic))).prod Q)
      {z | ∀ i : Fin (tuning p.toPublic).trials, QueryPlan.sampledEval g (fun j => ξ (j / 2) z.2)
        (trialPlan p.toPublic (tuning p.toPublic) (z.1 i)) (trialCalls (tuning p.toPublic) * i.val) = none} ≤
      ENNReal.ofReal (p.ε ^ 6 / (10 ^ 35 * StochasticEqualityTuning.scale p.toPublic ^ 38)))
    (hPB : ((seedLaw (tuning p.toPublic) : Measure (Seed (tuning p.toPublic))).prod Q)
      {z | ∃ i : Fin (tuning p.toPublic).trials, ¬ replyAccurate p.toPublic (tuning p.toPublic).validationTolerance
        (StochasticEqualityModel.truth I (trialPoint p.toPublic (tuning p.toPublic) g (fun j => ξ j z.2)
          (z.1 i) (trialSamples (tuning p.toPublic) * i.val)))
        (trialEstimate p.toPublic (tuning p.toPublic) g (fun j => ξ j z.2)
          (z.1 i) (trialSamples (tuning p.toPublic) * i.val))} ≤
      ENNReal.ofReal (p.ε ^ 6 / (10 ^ 35 * StochasticEqualityTuning.scale p.toPublic ^ 38))) :
    let y := fun z : Seed (tuning p.toPublic) × Ξ => QueryPlan.sampledEval g
      (fun j => ξ (j / 2) z.2) (plan p.toPublic (tuning p.toPublic) z.1) 0
    Integrable (fun z => ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 +
      ‖I.c (y z).1‖ ^ 2) ((seedLaw (tuning p.toPublic) : Measure (Seed (tuning p.toPublic))).prod Q) ∧
    (∫ z, ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 +
      ‖I.c (y z).1‖ ^ 2 ∂((seedLaw (tuning p.toPublic) : Measure (Seed (tuning p.toPublic))).prod Q)) ≤ p.ε ^ 2 := by
  let cfg := tuning p.toPublic
  let S := StochasticEqualityTuning.scale p.toPublic
  let μ := (seedLaw cfg : Measure (Seed cfg)).prod Q
  let y := fun z : Seed cfg × Ξ => QueryPlan.sampledEval g (fun j => ξ (j / 2) z.2) (plan p.toPublic cfg z.1) 0
  let f := fun z => ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 + ‖I.c (y z).1‖ ^ 2
  let A := {z : Seed cfg × Ξ | ∀ i : Fin cfg.trials,
    QueryPlan.sampledEval g (fun j => ξ (j / 2) z.2) (trialPlan p.toPublic cfg (z.1 i)) (trialCalls cfg * i.val) = none}
  let B := {z : Seed cfg × Ξ | ∃ i : Fin cfg.trials, ¬ replyAccurate p.toPublic cfg.validationTolerance
    (StochasticEqualityModel.truth I (trialPoint p.toPublic cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val)))
    (trialEstimate p.toPublic cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val))}
  have hpoint (i : Fin cfg.trials) : Measurable (fun z : Seed cfg × Ξ =>
      trialPoint p.toPublic cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val)) := by
    have hh : Measurable (fun z : Fin cfg.steps × (ℕ → Ω) => trialPoint p.toPublic cfg g z.2 z.1 (trialSamples cfg * i.val)) :=
      measurable_from_prod_countable_right fun k => measurable_trialPoint p.toPublic cfg g hg k _
    have hpair : Measurable (fun z : Seed cfg × Ξ => (z.1 i, fun j => ξ j z.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk (hξ.comp measurable_snd)
    exact hh.comp hpair
  have hest (i : Fin cfg.trials) : Measurable (fun z : Seed cfg × Ξ =>
      trialEstimate p.toPublic cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val)) := by
    have hh : Measurable (fun z : Fin cfg.steps × (ℕ → Ω) => trialEstimate p.toPublic cfg g z.2 z.1 (trialSamples cfg * i.val)) :=
      measurable_from_prod_countable_right fun k => measurable_trialEstimate p.toPublic cfg g hg k _
    have hpair : Measurable (fun z : Seed cfg × Ξ => (z.1 i, fun j => ξ j z.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk (hξ.comp measurable_snd)
    exact hh.comp hpair
  have hA : MeasurableSet A := by
    dsimp [A]
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hcall : trialCalls cfg * i.val = 2 * (trialSamples cfg * i.val) := by rw [trial_calls]; ring
    have he (z : Seed cfg × Ξ) := sampled_trial p.toPublic cfg g (fun j => ξ j z.2) (z.1 i) (trialSamples cfg * i.val)
    rw [← hcall] at he
    simp_rw [he]
    exact measurableSet_validate_none p.toPublic cfg _ _ (hest i)
  have hB : MeasurableSet B := by
    dsimp [B]
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (measurableSet_replyAccurate p.toPublic cfg.validationTolerance _ _
      ((StochasticEqualityModel.admissible_truth_measurable p hp I O hI).comp (hpoint i)) (hest i)).compl
  have hy : Measurable y := (measurable_sampled_output p.toPublic cfg g hg).comp
    (measurable_fst.prodMk (hξ.comp measurable_snd))
  have hf : Measurable f := StochasticEqualityModel.admissible_residual_measurable p hp I O hI y hy
  have hS0 : 0 < S := by have hh := (StochasticEqualityTuning.scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hh := integral_two_failures μ f hf hA hB
    (show 0 ≤ 10 ^ 33 * S ^ 38 / p.ε ^ 4 by positivity)
    (show 0 ≤ p.ε ^ 2 / 4 by positivity)
    (show 0 ≤ p.ε ^ 6 / (10 ^ 35 * S ^ 38) by positivity)
    (fun z => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun z => admissible_output_envelope p hp I O hI g (fun j => ξ j z.2) z.1)
    (fun z ha hb => admissible_selected_sound p hp I O hI g (fun j => ξ j z.2) z.1 ha (by
      simpa only [B, Set.mem_ofPred_eq, not_exists, not_not] using hb)) hPA hPB
  refine ⟨hh.1, hh.2.trans ?_⟩
  have he : p.ε ^ 2 / 4 + 2 * (10 ^ 33 * S ^ 38 / p.ε ^ 4) *
      (p.ε ^ 6 / (10 ^ 35 * S ^ 38)) = 27 * p.ε ^ 2 / 100 := by
    field_simp
    ring
  rw [he]
  nlinarith only [sq_nonneg p.ε]

lemma admissible_expected_output {Ω : Type} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Point p.d → Ω → Reply p.toPublic) (hg : Measurable (Function.uncurry g))
    (hi : ∀ y, Integrable (g y) P)
    (hmean : ∀ y, ∫ w, g y w ∂P = StochasticEqualityModel.truth I y)
    (hnoise2 : ∀ y, Integrable (fun w => ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2) P)
    (hnoise : ∀ y, (∫ w, ‖pack p.toPublic (g y w) -
      pack p.toPublic (StochasticEqualityModel.truth I y)‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (hdiff2 : ∀ y z, Integrable (fun w => ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2) P)
    (hdiff : ∀ y z, (∫ w, ‖pack p.toPublic (g y w) - pack p.toPublic (g z w)‖ ^ 2 ∂P) ≤
      p.Lnoise ^ 2 * ‖y - z‖ ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] {ξ : ℕ → Ξ → Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure Q] (hsamples : IID ξ P Q) :
    let y := fun z : Seed (tuning p.toPublic) × Ξ => QueryPlan.sampledEval g
      (fun j => ξ (j / 2) z.2) (plan p.toPublic (tuning p.toPublic) z.1) 0
    Integrable (fun z => ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 +
      ‖I.c (y z).1‖ ^ 2) ((seedLaw (tuning p.toPublic) : Measure (Seed (tuning p.toPublic))).prod Q) ∧
    (∫ z, ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 +
      ‖I.c (y z).1‖ ^ 2 ∂((seedLaw (tuning p.toPublic) : Measure (Seed (tuning p.toPublic))).prod Q)) ≤ p.ε ^ 2 := by
  apply expected_output_of_tails p hp I O hI g hg ξ (Measurable.of_eval hsamples.measurable) Q
  · have hh := admissible_all_trials_rejected p hp I O hI P g hg hi hmean hnoise2 hnoise hdiff2 hdiff hsamples
    apply hh.trans
    have hb := ENNReal.ofReal_le_ofReal (StochasticEqualityTuning.tuning_amplification_failure p hp).1
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hb
  · have hS0 : 0 < StochasticEqualityTuning.scale p.toPublic := by
      have hh := (StochasticEqualityTuning.scale_bounds p hp).1
      linarith only [hh]
    have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
    have ht : 0 < (tuning p.toPublic).validationTolerance := by
      change 0 < p.ε / (10 ^ 6 * StochasticEqualityTuning.scale p.toPublic ^ 7)
      positivity
    have hh := all_validation_failure p.toPublic (tuning p.toPublic) hsamples g hg
      (StochasticEqualityModel.truth I) (StochasticEqualityModel.admissible_truth_measurable p hp I O hI)
      hi hmean hnoise2 hnoise ht (StochasticEqualityTuning.tuning_robust_precision p hp).2
    apply hh.trans
    have hb := ENNReal.ofReal_le_ofReal (StochasticEqualityTuning.tuning_amplification_failure p hp).2
    have he : ENNReal.ofReal (3 * ((tuning p.toPublic).trials : ℝ) *
        (1 / 2 : ℝ) ^ ((tuning p.toPublic).validationGroups : ℕ)) =
        3 * ((tuning p.toPublic).trials : ℝ≥0∞) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ ((tuning p.toPublic).validationGroups : ℕ)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    rw [he] at hb
    exact hb

lemma admissible_execution (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (Point p.d) (Reply p.toPublic)) (hI : spec.admissible p I O)
    (K : ℕ) (hK : calls (tuning p.toPublic) ≤ K) :
    spec.successful p I
      (fun z : (algorithm p.toPublic).Seed × ((k : ℕ) → O.Seed k) => output p.toPublic O K z.1 z.2)
      ⟨((algorithm p.toPublic).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨g, P, Q, ξ, hsamples, hO, hg, hi, hmean, hnoise2, hnoise, hdiff2, hdiff⟩ :=
    StochasticEqualityModel.admissible_oracle p I O hI
  subst O
  let cfg := tuning p.toPublic
  let pair : p.Ξ → ℕ → p.Ω := fun z n => ξ (n / 2) z
  let O : Oracle (Point p.d) (Reply p.toPublic) :=
    { Seed := fun _ => p.Ω, law := Q.map pair, answer := fun _ (_, x) w => g x w }
  let y : Seed cfg × (ℕ → p.Ω) → Point p.d × Point p.m :=
    fun z => QueryPlan.sampledEval g z.2 (plan p.toPublic cfg z.1) 0
  let f := fun z => ‖gradient I.f (y z).1 + (fderiv ℝ I.c (y z).1).adjoint (y z).2‖ ^ 2 + ‖I.c (y z).1‖ ^ 2
  let μ := (seedLaw cfg : Measure (Seed cfg)).prod (Q : Measure p.Ξ)
  let ν := (seedLaw cfg : Measure (Seed cfg)).prod (Q.map pair : Measure (ℕ → p.Ω))
  let φ : Seed cfg × p.Ξ → Seed cfg × (ℕ → p.Ω) := fun z => (z.1, pair z.2)
  have hpair : Measurable pair := Measurable.of_eval fun n => hsamples.measurable (n / 2)
  have hmpPair : MeasurePreserving pair (Q : Measure p.Ξ) (Q.map pair : Measure (ℕ → p.Ω)) := ⟨hpair, rfl⟩
  have hmp0 := (MeasurePreserving.id (seedLaw cfg : Measure (Seed cfg))).prod hmpPair
  have hφ : Prod.map id pair = φ := by funext z; rfl
  rw [hφ] at hmp0
  have hmp : MeasurePreserving φ μ ν := hmp0
  have hy : Measurable y := measurable_raw_output p.toPublic cfg g hg
  have hf : Measurable f := StochasticEqualityModel.admissible_residual_measurable p hp I O hI y hy
  have hE := admissible_expected_output p hp I O hI (P : Measure p.Ω) g hg hi hmean hnoise2 hnoise hdiff2 hdiff hsamples
  have hcomp : Integrable (f ∘ φ) μ := hE.1
  have hfint : Integrable f ν := (hmp.integrable_comp hf.aestronglyMeasurable).mp hcomp
  have hfm : AEStronglyMeasurable f (μ.map φ) := by rw [hmp.map_eq]; exact hf.aestronglyMeasurable
  have he := integral_map hmp.measurable.aemeasurable hfm
  rw [hmp.map_eq] at he
  have hbound : (∫ z, f z ∂ν) ≤ p.ε ^ 2 := he.trans_le hE.2
  have hout : (fun z : Seed cfg × (ℕ → p.Ω) => output p.toPublic O K z.1 z.2) = y := by
    funext z
    exact execute_eq p.toPublic (Q.map pair) g z.1 z.2 K hK
  change spec.successful p I (fun z : Seed cfg × (ℕ → p.Ω) => output p.toPublic O K z.1 z.2)
    ⟨ν, inferInstance⟩
  rw [hout]
  have hspace (d : ℕ) : WithLp.measurableSpace 2 (Fin d → ℝ) = borel (Point d) :=
    @BorelSpace.measurable_eq (Point d) _ (WithLp.measurableSpace 2 (Fin d → ℝ))
      (PiLp.borelSpace (X := fun _ : Fin d => ℝ) 2)
  have hh : Measurable y ∧ Integrable f ν ∧ (∫ z, f z ∂ν) ≤ p.ε ^ 2 := ⟨hy, hfint, hbound⟩
  simpa (config := { instances := true }) only [spec, hspace, f, ProbabilityMeasure.coe_mk] using hh

end LongTails.Proofs.StochasticEqualityAmplification
