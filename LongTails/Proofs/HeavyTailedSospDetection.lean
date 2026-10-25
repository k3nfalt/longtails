import LongTails.Proofs.HeavyTailedCurvatureGeometry
import LongTails.Proofs.HeavyTailedRayleighValidation
import LongTails.Proofs.HeavyTailedSospExecution
import LongTails.Proofs.HeavyTailedProbeExecution
import LongTails.Proofs.HeavyTailedSospEpochIntegration

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSospDetection

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedSospExecution HeavyTailedProductProcess

lemma validation_prefix (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (trial : ℕ) (accepted : Option (Space p)) (v : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (l : ℕ) (hl : l < max 1 c.meanBatch * max 1 c.groups) :
    trajectory (sampleStep p c g H) l { s with phase := .validate trial accepted v [] } ξ =
      { s with phase := .validate trial accepted v (((List.range l).map (fun k => inner ℝ v (H s.point (ξ k).2 v))).reverse) } := by
  induction l with
  | zero => simp [trajectory]
  | succ l ih =>
    rw [trajectory_succ_last, ih (by omega)]
    simp only [sampleStep, query, update]
    have hlen : (inner ℝ v (H s.point (ξ l).2 v) ::
        ((List.range l).map (fun k => inner ℝ v (H s.point (ξ k).2 v))).reverse).length <
        max 1 c.meanBatch * max 1 c.groups := by simpa using hl
    simp only [hlen, ↓reduceIte]
    simp [List.range_succ]

noncomputable def validationEnd (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p)) (v : Space p) (values : List ℝ) : State p :=
  let a := if LongTails.Algorithms.HeavyTailedRayleighMedian.output (max 1 c.meanBatch)
      (max 1 c.groups) values ≤ -2 * c.γ then accepted.or (some v) else accepted
  if trial + 1 < max 1 c.repeats then { s with phase := .probeInit (trial + 1) a }
  else match a with
    | none => startCycle p c { s with cycleIndex := s.cycleIndex + 1 }
    | some w => { s with phase := .ncInit w }

lemma validation_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (trial : ℕ) (accepted : Option (Space p)) (v : Space p)
    (ξ : ℕ → Aux p c × p.Ω) :
    trajectory (sampleStep p c g H) (max 1 c.meanBatch * max 1 c.groups)
      { s with phase := .validate trial accepted v [] } ξ =
    validationEnd p c s trial accepted v
      ((List.range (max 1 c.meanBatch * max 1 c.groups)).map
        (fun k => inner ℝ v (H s.point (ξ k).2 v))) := by
  let K := max 1 c.meanBatch * max 1 c.groups
  have hK : 0 < K := by dsimp only [K]; positivity
  have heq : K = K - 1 + 1 := by omega
  change trajectory (sampleStep p c g H) K _ ξ = _
  rw [heq, trajectory_succ_last, validation_prefix p c g H s trial accepted v ξ (K - 1) (by omega)]
  simp only [sampleStep, query, update]
  have hlen : ¬(inner ℝ v (H s.point (ξ (K - 1)).2 v) ::
      ((List.range (K - 1)).map (fun k => inner ℝ v (H s.point (ξ k).2 v))).reverse).length <
      max 1 c.meanBatch * max 1 c.groups := by simp; omega
  simp only [hlen, ↓reduceIte]
  have hlist : (inner ℝ v (H s.point (ξ (K - 1)).2 v) ::
      ((List.range (K - 1)).map (fun k => inner ℝ v (H s.point (ξ k).2 v))).reverse).reverse =
      (List.range K).map (fun k => inner ℝ v (H s.point (ξ k).2 v)) := by
    rw [heq, List.range_succ]
    simp
  simp only [hlist]
  unfold validationEnd
  split_ifs
  all_goals try rfl

noncomputable def localProbe (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (l : ℕ) : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d :=
  LongTails.Algorithms.HeavyTailedEnergyProbe.run c.shift c.η
    (fun k v => H x (ξ k).2 v) l
    (LongTails.Algorithms.HeavyTailedEnergyProbe.initialState (ξ 0).1.2.2.1 (ξ 0).1.2.2.2.val)

lemma localProbe_index (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (l : ℕ) : (localProbe p c H x ξ l).index = l := by
  have hh := HeavyTailedProbeExecution.run_metadata c.shift c.η (fun k v => H x (ξ k).2 v) l
    (LongTails.Algorithms.HeavyTailedEnergyProbe.initialState (ξ 0).1.2.2.1 (ξ 0).1.2.2.2.val)
  simpa [localProbe, LongTails.Algorithms.HeavyTailedEnergyProbe.initialState] using hh.1

lemma localProbe_zero (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) : localProbe p c H x ξ 0 =
      LongTails.Algorithms.HeavyTailedEnergyProbe.initialState (ξ 0).1.2.2.1 (ξ 0).1.2.2.2.val := rfl

lemma localProbe_succ (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (l : ℕ) : localProbe p c H x ξ (l + 1) =
      LongTails.Algorithms.HeavyTailedEnergyProbe.step c.shift c.η (localProbe p c H x ξ l)
        (H x (ξ l).2 (localProbe p c H x ξ l).vector) := by
  unfold localProbe
  rw [HeavyTailedProbeExecution.run_succ]
  change LongTails.Algorithms.HeavyTailedEnergyProbe.step c.shift c.η _
    (H x (ξ (localProbe p c H x ξ l).index).2 _) = _
  rw [localProbe_index]

lemma probe_prefix (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (trial : ℕ) (accepted : Option (Space p))
    (ξ : ℕ → Aux p c × p.Ω) (l : ℕ) (hl : l < max 1 c.probeSteps) :
    trajectory (sampleStep p c g H) l { s with phase := .probeInit trial accepted } ξ =
      if l = 0 then { s with phase := .probeInit trial accepted }
      else { s with phase := .probe trial accepted (localProbe p c H s.point ξ l) } := by
  induction l with
  | zero => simp [trajectory]
  | succ l ih =>
    rw [trajectory_succ_last, ih (by omega)]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    by_cases hl0 : l = 0
    · subst l
      simp only [↓reduceIte, sampleStep, query, update, probeReply]
      have hindex : (LongTails.Algorithms.HeavyTailedEnergyProbe.step c.shift c.η
          (LongTails.Algorithms.HeavyTailedEnergyProbe.initialState (ξ 0).1.2.2.1 (ξ 0).1.2.2.2.val)
          (H s.point (ξ 0).2 (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector (ξ 0).1.2.2.1))).index
          < max 1 c.probeSteps := by simpa [LongTails.Algorithms.HeavyTailedEnergyProbe.step,
            LongTails.Algorithms.HeavyTailedEnergyProbe.initialState] using hl
      simp only [hindex, ↓reduceIte, localProbe_succ, localProbe_zero]
      rfl
    · simp only [hl0, ↓reduceIte, sampleStep, query, update, probeReply]
      have hindex : (LongTails.Algorithms.HeavyTailedEnergyProbe.step c.shift c.η
          (localProbe p c H s.point ξ l)
          (H s.point (ξ l).2 (localProbe p c H s.point ξ l).vector)).index < max 1 c.probeSteps := by
        simpa only [LongTails.Algorithms.HeavyTailedEnergyProbe.step, localProbe_index] using hl
      simp only [hindex, ↓reduceIte, localProbe_succ]

lemma probe_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (trial : ℕ) (accepted : Option (Space p))
    (ξ : ℕ → Aux p c × p.Ω) :
    trajectory (sampleStep p c g H) (max 1 c.probeSteps)
      { s with phase := .probeInit trial accepted } ξ =
      { s with phase := .validate trial accepted (localProbe p c H s.point ξ (max 1 c.probeSteps)).selected [] } := by
  let T := max 1 c.probeSteps
  have hT : 0 < T := by dsimp only [T]; omega
  have heq : T = T - 1 + 1 := by omega
  change trajectory (sampleStep p c g H) T _ ξ = _
  rw [heq, trajectory_succ_last, probe_prefix p c g H s trial accepted ξ (T - 1) (by omega)]
  by_cases h0 : T - 1 = 0
  · have hT1 : max 1 c.probeSteps = 1 := by omega
    simp only [h0, ↓reduceIte, sampleStep, query, update, probeReply]
    have hlocal := localProbe_succ p c H s.point ξ 0
    simp only [hT1, hlocal, localProbe_zero,
      LongTails.Algorithms.HeavyTailedEnergyProbe.step,
      LongTails.Algorithms.HeavyTailedEnergyProbe.initialState]
    rfl
  · simp only [h0, ↓reduceIte, sampleStep, query, update, probeReply]
    have hindex : ¬(LongTails.Algorithms.HeavyTailedEnergyProbe.step c.shift c.η
        (localProbe p c H s.point ξ (T - 1))
        (H s.point (ξ (T - 1)).2 (localProbe p c H s.point ξ (T - 1)).vector)).index <
        max 1 c.probeSteps := by
      simp only [LongTails.Algorithms.HeavyTailedEnergyProbe.step, localProbe_index]
      omega
    simp only [hindex, ↓reduceIte]
    have hlast : localProbe p c H s.point ξ (max 1 c.probeSteps) =
        LongTails.Algorithms.HeavyTailedEnergyProbe.step c.shift c.η (localProbe p c H s.point ξ (T - 1))
          (H s.point (ξ (T - 1)).2 (localProbe p c H s.point ξ (T - 1)).vector) := by
      change localProbe p c H s.point ξ T = _
      conv_lhs => rw [heq]
      exact localProbe_succ p c H s.point ξ (T - 1)
    simp only [hlast]

lemma validationEnd_phase (p : Params) (c : Config) (s : State p) (phase : Phase p)
    (trial : ℕ) (accepted : Option (Space p)) (v : Space p) (values : List ℝ) :
    validationEnd p c { s with phase := phase } trial accepted v values =
      validationEnd p c s trial accepted v values := by
  unfold validationEnd
  split_ifs
  all_goals try rfl

lemma trial_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (trial : ℕ) (accepted : Option (Space p))
    (ξ : ℕ → Aux p c × p.Ω) :
    let T := max 1 c.probeSteps
    let K := max 1 c.meanBatch * max 1 c.groups
    let v := (localProbe p c H s.point ξ T).selected
    trajectory (sampleStep p c g H) (T + K) { s with phase := .probeInit trial accepted } ξ =
      validationEnd p c s trial accepted v
        ((List.range K).map (fun k => inner ℝ v (H s.point (ξ (T + k)).2 v))) := by
  intro T K v
  rw [HeavyTailedSospEpochIntegration.trajectory_add, probe_complete]
  rw [validation_complete]

lemma aux_probe_seed_preserving (p : Params) (c : Config) [NeZero (max 1 c.probeSteps)] :
    MeasureTheory.MeasurePreserving (fun a : Aux p c => a.2.2)
      (auxLaw p c : MeasureTheory.Measure (Aux p c))
      ((PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure) := by
  let U : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 1)
  let : MeasureTheory.IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let S := (PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod
    (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure
  change MeasureTheory.MeasurePreserving (fun a : Aux p c => a.2.2)
    (U.prod ((PMF.uniformOfFintype Bool).toMeasure.prod S)) S
  exact (MeasureTheory.measurePreserving_snd (μ := (PMF.uniformOfFintype Bool).toMeasure) (ν := S)).comp
    (MeasureTheory.measurePreserving_snd (μ := U) (ν := (PMF.uniformOfFintype Bool).toMeasure.prod S))

lemma paired_probe_seed_oracle_preserving (p : Params) (c : Config) [NeZero (max 1 c.probeSteps)]
    (P0 : MeasureTheory.Measure p.Ω) [MeasureTheory.IsProbabilityMeasure P0] :
    MeasureTheory.MeasurePreserving
      (fun ξ : ℕ → Aux p c × p.Ω => ((ξ 0).1.2.2, fun k => (ξ k).2))
      (MeasureTheory.Measure.infinitePi fun _ : ℕ => (auxLaw p c : MeasureTheory.Measure (Aux p c)).prod P0)
      (((PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure).prod
        (MeasureTheory.Measure.infinitePi fun _ : ℕ => P0)) := by
  let Q := (auxLaw p c : MeasureTheory.Measure (Aux p c))
  have hzip := HeavyTailedTapeExecution.zip_streams_preserving Q P0
  have hseed := (aux_probe_seed_preserving p c).comp (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) 0)
  have hprod := hseed.prod (MeasureTheory.MeasurePreserving.id (MeasureTheory.Measure.infinitePi fun _ : ℕ => P0))
  have hF : Measurable (fun ξ : ℕ → Aux p c × p.Ω => ((ξ 0).1.2.2, fun k => (ξ k).2)) := by fun_prop
  refine ⟨hF, ?_⟩
  rw [← hzip.map_eq, MeasureTheory.Measure.map_map hF hzip.measurable]
  exact hprod.map_eq

lemma localProbe_selected_path (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) :
    (localProbe p c H x ξ (max 1 c.probeSteps)).selected =
      HeavyTailedSpectralEnergy.initialPath
        (fun ω => c.shift • ContinuousLinearMap.id ℝ _ - H x ω) c.η
        ((ξ 0).1.2.2.1, fun k => (ξ k).2) (ξ 0).1.2.2.2.val := by
  unfold localProbe
  rw [HeavyTailedProbeExecution.run_selected c.shift c.η _ _ _ rfl (ξ 0).1.2.2.2.isLt]
  rw [HeavyTailedProbeExecution.run_vector_eq_normalizedPath c.shift c.η _ _ _ rfl]
  simp only [HeavyTailedSpectralEnergy.initialPath, HeavyTailedProbeExecution.shifted_step_identity,
    LongTails.Algorithms.HeavyTailedEnergyProbe.initialState]

lemma localProbe_selected_norm (p : Params) (hd : 0 < p.d) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) :
    ‖(localProbe p c H x ξ (max 1 c.probeSteps)).selected‖ = 1 := by
  rw [localProbe_selected_path]
  exact HeavyTailedSpectralEnergy.initialPath_norm hd _ _ _ _

lemma localProbe_probability (p : Params) (c : Config) [NeZero (max 1 c.probeSteps)]
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (hH : Measurable (H x))
    (P0 : MeasureTheory.Measure p.Ω) [MeasureTheory.IsProbabilityMeasure P0]
    (S : Set (Space p)) (hS : MeasurableSet S) :
    (MeasureTheory.Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : MeasureTheory.Measure (Aux p c)).prod P0).real
      {ξ | (localProbe p c H x ξ (max 1 c.probeSteps)).selected ∈ S} =
    (((PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure).prod (MeasureTheory.Measure.infinitePi fun _ : ℕ => P0)).real
      {z | HeavyTailedSpectralEnergy.initialPath
        (fun ω => c.shift • ContinuousLinearMap.id ℝ _ - H x ω) c.η
        (z.1.1, z.2) z.1.2.val ∈ S} := by
  have hB : Measurable (fun ω => c.shift • ContinuousLinearMap.id ℝ (Space p) - H x ω) :=
    measurable_const.sub hH
  have hp : Measurable (fun z : ((Fin p.d → Bool) × Fin (max 1 c.probeSteps)) × (ℕ → p.Ω) =>
      HeavyTailedSpectralEnergy.initialPath
        (fun ω => c.shift • ContinuousLinearMap.id ℝ _ - H x ω) c.η
        (z.1.1, z.2) z.1.2.val) := by
    have hm : Measurable (fun z : ((Fin p.d → Bool) × (ℕ → p.Ω)) × Fin (max 1 c.probeSteps) =>
        HeavyTailedSpectralEnergy.initialPath
          (fun ω => c.shift • ContinuousLinearMap.id ℝ _ - H x ω) c.η z.1 z.2.val) := measurable_from_prod_countable_left
      (fun i : Fin (max 1 c.probeSteps) => by
        have hsm : MeasureTheory.StronglyMeasurable (fun z : (Fin p.d → Bool) × (ℕ → p.Ω) =>
            HeavyTailedSpectralEnergy.initialPath
              (fun ω => c.shift • ContinuousLinearMap.id ℝ _ - H x ω) c.η z i.val) := by
          let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
          exact (HeavyTailedSpectralEnergy.initialPath_measurable
            (fun ω => c.shift • ContinuousLinearMap.id ℝ _ - H x ω) hB c.η i.val).stronglyMeasurable
        exact hsm.measurable)
    have hswap : Measurable (fun z : ((Fin p.d → Bool) × Fin (max 1 c.probeSteps)) × (ℕ → p.Ω) =>
      ((z.1.1, z.2), z.1.2)) := by fun_prop
    have hc := hm.comp hswap
    exact hc
  have heq := (paired_probe_seed_oracle_preserving p c P0).measureReal_preimage
    (hS.preimage hp).nullMeasurableSet
  simpa only [Set.preimage, Set.mem_ofPred_eq, localProbe_selected_path] using heq

lemma validation_accepts_negative {γ curvature estimate : ℝ} (hγ : 0 ≤ γ)
    (hc : curvature ≤ -3 * γ) (he : |estimate - curvature| ≤ γ / 2) :
    estimate ≤ -2 * γ := by
  have hu := (abs_le.mp he).2
  linarith

lemma validation_acceptance_sound {γ curvature estimate : ℝ}
    (ha : estimate ≤ -2 * γ) (he : |estimate - curvature| ≤ γ / 2) :
    curvature ≤ -3 * γ / 2 := by
  have hl := (abs_le.mp he).1
  linarith

noncomputable def trialCandidate (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) : Space p :=
  (localProbe p c H x ξ (max 1 c.probeSteps)).selected

noncomputable def trialEstimate (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) : ℝ :=
  let v := trialCandidate p c H x ξ
  LongTails.Algorithms.HeavyTailedRayleighMedian.output (max 1 c.meanBatch) (max 1 c.groups)
    ((List.range (max 1 c.meanBatch * max 1 c.groups)).map
      (fun k => inner ℝ v (H x (ξ (max 1 c.probeSteps + k)).2 v)))

noncomputable def trialChoice (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) : Option (Space p) :=
  if trialEstimate p c H x ξ ≤ -2 * c.γ then some (trialCandidate p c H x ξ) else none

noncomputable def detectorChoice (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) : ℕ → Option (Space p)
  | 0 => none
  | j + 1 => (detectorChoice p c H x ξ j).or
      (trialChoice p c H x (fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)))

lemma detector_prefix (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) (j : ℕ) (hj : j < max 1 c.repeats) :
    trajectory (sampleStep p c g H)
      (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups))
      { s with phase := .probeInit 0 none } ξ =
      { s with phase := .probeInit j (detectorChoice p c H s.point ξ j) } := by
  induction j with
  | zero => simp [trajectory, detectorChoice]
  | succ j ih =>
    rw [Nat.succ_mul, HeavyTailedSospEpochIntegration.trajectory_add, ih (by omega)]
    rw [trial_complete]
    simp only [validationEnd, hj, ↓reduceIte]
    change { s with phase := (.probeInit (j + 1)
      (if trialEstimate p c H s.point
          (fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)) ≤ -2 * c.γ
        then (detectorChoice p c H s.point ξ j).or
          (some (trialCandidate p c H s.point
            (fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k))))
        else detectorChoice p c H s.point ξ j)) } = _
    rw [detectorChoice, trialChoice]
    split_ifs <;> simp_all only [Option.or_none]

lemma detector_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) :
    trajectory (sampleStep p c g H)
      (max 1 c.repeats * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups))
      { s with phase := .probeInit 0 none } ξ =
      match detectorChoice p c H s.point ξ (max 1 c.repeats) with
      | none => startCycle p c { s with cycleIndex := s.cycleIndex + 1 }
      | some v => { s with phase := .ncInit v } := by
  let R := max 1 c.repeats
  have hR : 0 < R := by dsimp only [R]; omega
  have hlast : R = R - 1 + 1 := by omega
  change trajectory (sampleStep p c g H)
      (R * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups)) _ ξ = _
  conv_lhs => rw [hlast, Nat.succ_mul]
  rw [HeavyTailedSospEpochIntegration.trajectory_add,
    detector_prefix p c g H s ξ (R - 1) (by omega), trial_complete]
  have hn : ¬R - 1 + 1 < max 1 c.repeats := by dsimp only [R]; omega
  change _ = match detectorChoice p c H s.point ξ R with | none => _ | some v => _
  conv_rhs => rw [hlast]
  simp only [validationEnd, hn, ↓reduceIte]
  change (match (if trialEstimate p c H s.point
      (fun k => ξ ((R - 1) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)) ≤ -2 * c.γ
    then (detectorChoice p c H s.point ξ (R - 1)).or
      (some (trialCandidate p c H s.point
        (fun k => ξ ((R - 1) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k))))
    else detectorChoice p c H s.point ξ (R - 1)) with
    | none => startCycle p c { s with cycleIndex := s.cycleIndex + 1 }
    | some v => { s with phase := .ncInit v }) = _
  rw [detectorChoice, trialChoice]
  split_ifs <;> simp only [Option.or_none]

lemma localProbe_prefix_congr (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ ζ : ℕ → Aux p c × p.Ω) (N : ℕ) (hN : 0 < N)
    (heq : ∀ k < N, ξ k = ζ k) (l : ℕ) (hl : l ≤ N) :
    localProbe p c H x ξ l = localProbe p c H x ζ l := by
  induction l with
  | zero => simp only [localProbe_zero, heq 0 hN]
  | succ l ih =>
    rw [localProbe_succ, localProbe_succ, ih (by omega), heq l (by omega)]

lemma localProbe_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (l : ℕ) :
    Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) => localProbe p c H z.1 z.2 l) := by
  induction l with
  | zero =>
    simp only [localProbe_zero]
    exact (HeavyTailedSospMeasurable.measurable_probe_initial p c).comp
      (((measurable_pi_apply 0).comp measurable_snd).fst)
  | succ l ih =>
    simp only [localProbe_succ]
    have hsample : Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) => (z.2 l).2) := by fun_prop
    have hoperator := hH.comp (measurable_fst.prodMk hsample)
    have hv := (HeavyTailedSospMeasurable.measurable_probe_vector p.d).comp ih
    have hr := isBoundedBilinearMap_apply.continuous.measurable.comp (hoperator.prodMk hv)
    have hm := (HeavyTailedSospMeasurable.measurable_probe_step p.d c.shift c.η).comp (ih.prodMk hr)
    exact hm

lemma trialCandidate_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) => trialCandidate p c H z.1 z.2) := by
  exact (HeavyTailedSospMeasurable.measurable_probe_selected p.d).comp
    (localProbe_measurable p c H hH (max 1 c.probeSteps))

open scoped OracleTemplate.AdaptiveList

lemma trialEstimate_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) => trialEstimate p c H z.1 z.2) := by
  have hv := trialCandidate_measurable p c H hH
  have hr (k : ℕ) : Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) =>
      inner ℝ (trialCandidate p c H z.1 z.2)
        (H z.1 (z.2 (max 1 c.probeSteps + k)).2 (trialCandidate p c H z.1 z.2))) := by
    have hs : Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) =>
        (z.2 (max 1 c.probeSteps + k)).2) := by fun_prop
    have ho := hH.comp (measurable_fst.prodMk hs)
    have ha := isBoundedBilinearMap_apply.continuous.measurable.comp (ho.prodMk hv)
    exact hv.inner ha
  have hlist (l : List ℕ) : Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) =>
      l.map (fun k => inner ℝ (trialCandidate p c H z.1 z.2)
        (H z.1 (z.2 (max 1 c.probeSteps + k)).2 (trialCandidate p c H z.1 z.2)))) := by
    induction l with
    | nil => exact measurable_const
    | cons k l ih =>
      exact (OracleTemplate.AdaptiveList.measurable_cons 0).comp ((hr k).prodMk ih)
  have hm := (HeavyTailedSospMeasurable.measurable_rayleigh_output
    (max 1 c.meanBatch) (max 1 c.groups)).comp
      (hlist (List.range (max 1 c.meanBatch * max 1 c.groups)))
  exact hm

open MeasureTheory

lemma localProbe_energy_probability (p : Params) (hd : 0 < p.d) (c : Config)
    (x : Space p) (ell γ q : ℝ)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (Hmean : Space p →L[ℝ] Space p) (hH : Measurable (H x))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hη : 0 < c.η) (hpq : p.p.HolderConjugate q) (hp2 : p.p ≤ 2)
    (hell : 0 ≤ ell) (hηell : c.η * ell ≤ 1) (hγ : 0 < γ) (hσ : 0 ≤ p.σh)
    (hpos : ∀ v, 0 ≤ ⟪v, (c.shift • ContinuousLinearMap.id ℝ (Space p) - Hmean) v⟫)
    (hnorm : ‖c.shift • ContinuousLinearMap.id ℝ (Space p) - Hmean‖ ≤ ell)
    (hi : ∀ v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ v, (∫ ω, H x ω v ∂P0) = Hmean v)
    (hpi : ∀ v, Integrable (fun ω => ‖H x ω v - Hmean v‖ ^ p.p) P0)
    (hb : ∀ v, (∫ ω, ‖H x ω v - Hmean v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (u : Space p) (hu : (c.shift • ContinuousLinearMap.id ℝ (Space p) - Hmean) u = ell • u)
    (hunit : ‖u‖ = 1)
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤ c.η * (max 1 c.probeSteps : ℕ) * γ)
    (hsmall : ((1 + c.η * ell) ^ p.p + 6 * c.η ^ p.p * p.σh ^ p.p) ^ max 1 c.probeSteps ≤
      (2 * (1 + c.η * ell) ^ max 1 c.probeSteps) ^ p.p)
    (hnoise : (max 1 c.probeSteps : ℕ) * (c.η ^ p.p * p.σh ^ p.p) ≤ (1 / 4 : ℝ) ^ q / 256) :
    (1 / 4 : ℝ) ^ q / 64 ≤
      (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | let v := trialCandidate p c H x ξ
        ell - ⟪v, (c.shift • ContinuousLinearMap.id ℝ (Space p) - Hmean) v⟫ ≤ γ} := by
  let : NeZero (max 1 c.probeSteps) := ⟨by omega⟩
  let A := c.shift • ContinuousLinearMap.id ℝ (Space p) - Hmean
  let B := fun ω => c.shift • ContinuousLinearMap.id ℝ (Space p) - H x ω
  have hB : Measurable B := measurable_const.sub hH
  have hshift (v : Space p) := HeavyTailedSpectralMoments.shifted_oracle_moments
    Hmean (H x) v c.shift p.p p.σh (hi v) (hm v) (hpi v) (hb v)
  have he := HeavyTailedSpectralEnergy.spectral_energy_probability
    P0 hd A B hB hη hpq hp2 hell hηell hγ hσ hpos hnorm
    (fun v => (hshift v).1) (fun v => (hshift v).2.1)
    (fun v => (hshift v).2.2.1) (fun v => (hshift v).2.2.2)
    hu hunit (max 1 c.probeSteps) htune hsmall hnoise
  let S := {v : Space p | ell - ⟪v, A v⟫ ≤ γ}
  have hS : MeasurableSet S := measurableSet_le
    (measurable_const.sub (measurable_id.inner A.continuous.measurable)) measurable_const
  have heq := localProbe_probability p c H x hH P0 S hS
  change (1 / 4 : ℝ) ^ q / 64 ≤
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | (localProbe p c H x ξ (max 1 c.probeSteps)).selected ∈ S}
  rw [heq]
  let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
  have hp : Measurable (fun z : ((Fin p.d → Bool) × (ℕ → p.Ω)) × Fin (max 1 c.probeSteps) =>
      HeavyTailedSpectralEnergy.initialPath B c.η z.1 z.2.val) :=
    measurable_from_prod_countable_left
      (fun i => HeavyTailedSpectralEnergy.initialPath_measurable B hB c.η i.val)
  have hs : MeasurableSet {z : ((Fin p.d → Bool) × (ℕ → p.Ω)) × Fin (max 1 c.probeSteps) |
      ell - ⟪HeavyTailedSpectralEnergy.initialPath B c.η z.1 z.2.val,
        A (HeavyTailedSpectralEnergy.initialPath B c.η z.1 z.2.val)⟫ ≤ γ} :=
    measurableSet_le (measurable_const.sub (hp.inner (A.continuous.measurable.comp hp))) measurable_const
  have hpres := HeavyTailedProbeExecution.swap_second_third_preserving
    (PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure
    (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure (Measure.infinitePi fun _ : ℕ => P0)
  have hs_eq := hpres.measureReal_preimage hs.nullMeasurableSet
  simpa only [Set.preimage, Set.mem_ofPred_eq, S, B] using hs_eq.symm ▸ he

lemma paired_oracle_stream_preserving (p : Params) (c : Config)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0] :
    MeasurePreserving (fun ξ : ℕ → Aux p c × p.Ω => fun k => (ξ k).2)
      (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0)
      (Measure.infinitePi fun _ : ℕ => P0) := by
  let : NeZero (max 1 c.probeSteps) := ⟨by omega⟩
  exact (measurePreserving_snd (μ :=
    (PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod
      (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure)
    (ν := Measure.infinitePi fun _ : ℕ => P0)).comp
      (paired_probe_seed_oracle_preserving p c P0)

lemma product_event_upper {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {S : Set (Ω × Ξ)} (hS : MeasurableSet S) {ν : ℝ}
    (hf : ∀ x, Q.real (Prod.mk x ⁻¹' S) ≤ ν) :
    (P.prod Q).real S ≤ ν := by
  let F : Ω × Ξ → ℝ := S.indicator 1
  have hFi : Integrable F (P.prod Q) := (integrable_const (1 : ℝ)).indicator hS
  have hinner (x : Ω) : (∫ y, F (x, y) ∂Q) = Q.real (Prod.mk x ⁻¹' S) := by
    change (∫ y, (Prod.mk x ⁻¹' S).indicator 1 y ∂Q) = _
    exact integral_indicator_one (hS.preimage measurable_prodMk_left)
  have hb := integral_mono hFi.integral_prod_left (integrable_const ν)
    (fun x => show (∫ y, F (x, y) ∂Q) ≤ ν from by rw [hinner]; exact hf x)
  rw [← integral_prod F hFi, integral_indicator_one hS, integral_const] at hb
  simpa using hb

lemma splice_streams_preserving {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ) :
    MeasurePreserving
      (fun z : (ℕ → Ω) × (ℕ → Ω) => fun k => if k < n then z.1 k else z.2 (k - n))
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => Q))
      (Measure.infinitePi fun _ : ℕ => Q) := by
  have hp := (OracleTemplate.StochasticGeneralized.prefix_preserving Q n).prod
    (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => Q))
  have hs := (OracleTemplate.StochasticGeneralized.splitStream_preserving Q n).symm
    (OracleTemplate.StochasticGeneralized.splitStream n)
  convert hs.comp hp using 1
  funext z k
  change (if k < n then z.1 k else z.2 (k - n)) =
    (if h : k < n then z.1 (⟨k, h⟩ : Fin n).val else z.2 (k - n))
  split <;> rfl

lemma scalar_validation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → ℝ) (ha : Measurable a) (n m : ℕ) :
    Measurable (fun ξ : ℕ → Ω => LongTails.Algorithms.HeavyTailedRayleighMedian.output n m
      ((List.range (n * m)).map (fun k => a (ξ k)))) := by
  have hlist (l : List ℕ) : Measurable (fun ξ : ℕ → Ω => l.map (fun k => a (ξ k))) := by
    induction l with
    | nil => exact measurable_const
    | cons k l ih =>
      exact (OracleTemplate.AdaptiveList.measurable_cons 0).comp
        ((ha.comp (measurable_pi_apply k)).prodMk ih)
  exact (HeavyTailedSospMeasurable.measurable_rayleigh_output n m).comp (hlist _)

lemma fixed_validation_probability (p : Params) (c : Config)
    (x v : Space p) (hv : ‖v‖ = 1)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (A : Space p →L[ℝ] Space p)
    (hH : Measurable (H x)) (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hγ : 0 < c.γ)
    (hi : Integrable (fun ω => H x ω v) P0)
    (hm : (∫ ω, H x ω v ∂P0) = A v)
    (hpi : Integrable (fun ω => ‖H x ω v - A v‖ ^ p.p) P0)
    (hb : (∫ ω, ‖H x ω v - A v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p)
    (htune : 6 * p.σh ^ p.p / ((max 1 c.meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤ (c.γ / 8) ^ p.p) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | c.γ / 2 < |LongTails.Algorithms.HeavyTailedRayleighMedian.output
        (max 1 c.meanBatch) (max 1 c.groups)
        ((List.range (max 1 c.meanBatch * max 1 c.groups)).map
          (fun k => inner ℝ v (H x (ξ k).2 v))) - inner ℝ v (A v)|} ≤
      Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8) := by
  have hscalar := HeavyTailedRayleighValidation.rayleigh_scalar_moments P0 (H x) A v hv
    (by linarith : 0 ≤ p.p) hi hm hpi hb
  have ha : Measurable (fun ω => inner ℝ v (H x ω v)) := by fun_prop
  have hpv := HeavyTailedRayleighValidation.scalar_output_probability P0 _ ha hp hp2 hγ
    hscalar.1 hscalar.2.1 hscalar.2.2.1 hscalar.2.2.2
    (max 1 c.meanBatch) (max 1 c.groups) (by omega) (by omega) htune
  have hf := scalar_validation_measurable _ ha (max 1 c.meanBatch) (max 1 c.groups)
  have hS := measurableSet_lt (measurable_const (a := c.γ / 2))
    (continuous_abs.measurable.comp (hf.sub_const (inner ℝ v (A v))))
  have heq := (paired_oracle_stream_preserving p c P0).measureReal_preimage hS.nullMeasurableSet
  simpa only [Set.preimage, Set.mem_ofPred_eq] using heq.symm ▸ hpv

lemma trial_splice_candidate (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ ζ : ℕ → Aux p c × p.Ω) :
    trialCandidate p c H x (fun k => if k < max 1 c.probeSteps then ξ k else ζ (k - max 1 c.probeSteps)) =
      trialCandidate p c H x ξ := by
  unfold trialCandidate
  congr 1
  exact localProbe_prefix_congr p c H x _ ξ (max 1 c.probeSteps) (by omega)
    (fun k hk => by simp only [hk, ↓reduceIte]) _ (le_refl _)

lemma trial_splice_estimate (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ ζ : ℕ → Aux p c × p.Ω) :
    trialEstimate p c H x (fun k => if k < max 1 c.probeSteps then ξ k else ζ (k - max 1 c.probeSteps)) =
      LongTails.Algorithms.HeavyTailedRayleighMedian.output (max 1 c.meanBatch) (max 1 c.groups)
        ((List.range (max 1 c.meanBatch * max 1 c.groups)).map
          (fun k => inner ℝ (trialCandidate p c H x ξ)
            (H x (ζ k).2 (trialCandidate p c H x ξ)))) := by
  unfold trialEstimate
  rw [trial_splice_candidate]
  have hn (k : ℕ) : ¬max 1 c.probeSteps + k < max 1 c.probeSteps := by omega
  simp only [hn, ↓reduceIte, Nat.add_sub_cancel_left]

lemma trial_validation_probability (p : Params) (hd : 0 < p.d) (c : Config)
    (x : Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (A : Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hγ : 0 < c.γ)
    (hi : ∀ v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ v, (∫ ω, H x ω v ∂P0) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖H x ω v - A v‖ ^ p.p) P0)
    (hb : ∀ v, (∫ ω, ‖H x ω v - A v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (htune : 6 * p.σh ^ p.p / ((max 1 c.meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤ (c.γ / 8) ^ p.p) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | c.γ / 2 < |trialEstimate p c H x ξ -
        inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|} ≤
      Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8) := by
  let Q := (auxLaw p c : Measure (Aux p c)).prod P0
  let E := {ξ : ℕ → Aux p c × p.Ω | c.γ / 2 < |trialEstimate p c H x ξ -
    inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|}
  have hv := (trialCandidate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have ht := (trialEstimate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (ht.sub (hv.inner (A.continuous.measurable.comp hv))))
  have hs := splice_streams_preserving Q (max 1 c.probeSteps)
  change (Measure.infinitePi fun _ : ℕ => Q).real E ≤ _
  rw [← hs.measureReal_preimage hE.nullMeasurableSet]
  apply product_event_upper _ _ (hE.preimage hs.measurable)
  intro ξ
  have hunit : ‖trialCandidate p c H x ξ‖ = 1 := localProbe_selected_norm p hd c H x ξ
  have hfixed := fixed_validation_probability p c x (trialCandidate p c H x ξ) hunit H A
    (hH.comp ((measurable_const (a := x)).prodMk measurable_id)) P0 hp hp2 hγ
    (hi _) (hm _) (hpi _) (by simpa only [hunit, Real.one_rpow, mul_one] using hb (trialCandidate p c H x ξ)) htune
  simpa only [E, Q, Set.preimage, Set.mem_ofPred_eq, trial_splice_candidate, trial_splice_estimate] using hfixed

lemma detectorChoice_some_origin (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (R : ℕ) (v : Space p)
    (hv : detectorChoice p c H x ξ R = some v) :
    ∃ j < R, trialChoice p c H x
      (fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)) = some v := by
  induction R with
  | zero => simp [detectorChoice] at hv
  | succ R ih =>
    rw [detectorChoice] at hv
    cases ha : detectorChoice p c H x ξ R with
    | none =>
      simp only [ha, Option.none_or] at hv
      exact ⟨R, by omega, hv⟩
    | some w =>
      simp only [ha, Option.some_or, Option.some.injEq] at hv
      subst w
      obtain ⟨j, hj, heq⟩ := ih ha
      exact ⟨j, by omega, heq⟩

lemma detectorChoice_none_iff (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (R : ℕ) :
    detectorChoice p c H x ξ R = none ↔ ∀ j < R, trialChoice p c H x
      (fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)) = none := by
  induction R with
  | zero => simp [detectorChoice]
  | succ R ih =>
    rw [detectorChoice]
    have hor (a b : Option (Space p)) : a.or b = none ↔ a = none ∧ b = none := by
      cases a <;> simp
    rw [hor, ih]
    constructor
    · rintro ⟨ha, hb⟩ j hj
      by_cases heq : j = R
      · simpa only [heq] using hb
      · exact ha j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h R (by omega)⟩

noncomputable def blockExtension {Ω : Type*} (n : ℕ) [NeZero n]
    (η : Fin n → Ω) : ℕ → Ω := fun k => η ⟨k % n, Nat.mod_lt k (Nat.pos_of_ne_zero (NeZero.ne n))⟩

lemma blockExtension_measurable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) [NeZero n] :
    Measurable (blockExtension (Ω := Ω) n) := by
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _

lemma blockExtension_prefix {Ω : Type*} (n : ℕ) [NeZero n]
    (η : Fin n → Ω) (k : ℕ) (hk : k < n) :
    blockExtension n η k = η ⟨k, hk⟩ := by
  unfold blockExtension
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hk)

lemma independent_block_failure {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (S : Set Ω) (hS : MeasurableSet S)
    (R : ℕ) (a : ℝ) (ha : a ≤ Q.real S) :
    (Measure.pi fun _ : Fin R => Q).real {z | ∀ j, z j ∉ S} ≤ Real.exp (-a * R) := by
  have heq : {z : Fin R → Ω | ∀ j, z j ∉ S} = Set.univ.pi (fun _ : Fin R => Sᶜ) := by
    ext z
    simp
  have hmass : (Measure.pi fun _ : Fin R => Q).real {z | ∀ j, z j ∉ S} = (Q.real Sᶜ) ^ R := by
    simp only [Measure.real, heq, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ENNReal.toReal_pow]
  rw [hmass]
  have hc : Q.real Sᶜ = 1 - Q.real S := by rw [measureReal_compl hS, probReal_univ]
  have hb : Q.real Sᶜ ≤ Real.exp (-a) := by
    have he := Real.add_one_le_exp (-a)
    rw [hc]
    linarith
  calc
    (Q.real Sᶜ) ^ R ≤ (Real.exp (-a)) ^ R := pow_le_pow_left₀ measureReal_nonneg hb R
    _ = Real.exp (-a * R) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma finite_prefix_amplification {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ) [NeZero n]
    (F : (ℕ → Ω) → E) (hF : Measurable F)
    (hprefix : ∀ ξ ζ, (∀ k < n, ξ k = ζ k) → F ξ = F ζ)
    (S : Set E) (hS : MeasurableSet S) (R : ℕ) (a : ℝ)
    (ha : a ≤ (Measure.infinitePi fun _ : ℕ => Q).real (F ⁻¹' S)) :
    (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | ∀ j : Fin R, F (fun k => ξ (j * n + k)) ∉ S} ≤ Real.exp (-a * R) := by
  let B : (Fin n → Ω) → E := fun η => F (blockExtension n η)
  have hB : Measurable B := hF.comp (blockExtension_measurable n)
  have hBS : MeasurableSet (B ⁻¹' S) := hS.preimage hB
  have hrecover (ξ : ℕ → Ω) : B (fun k : Fin n => ξ k) = F ξ := by
    apply hprefix
    intro k hk
    exact blockExtension_prefix n (fun k : Fin n => ξ k) k hk
  have hsingle : a ≤ (Measure.pi fun _ : Fin n => Q).real (B ⁻¹' S) := by
    rw [← (OracleTemplate.StochasticGeneralized.prefix_preserving Q n).measureReal_preimage
      hBS.nullMeasurableSet]
    simpa only [Set.preimage_preimage, Function.comp_def, hrecover] using ha
  have hb := independent_block_failure (Measure.pi fun _ : Fin n => Q)
    (B ⁻¹' S) hBS R a hsingle
  have hAll : MeasurableSet {z : Fin R → (Fin n → Ω) | ∀ j, B (z j) ∉ S} := by
    have heq : {z : Fin R → (Fin n → Ω) | ∀ j, B (z j) ∉ S} =
        ⋂ j : Fin R, {z | B (z j) ∉ S} := by ext z; simp
    rw [heq]
    exact MeasurableSet.iInter fun j => (hBS.preimage (measurable_pi_apply j)).compl
  change (Measure.pi fun _ : Fin R => Measure.pi fun _ : Fin n => Q).real
    {z | ∀ j, B (z j) ∉ S} ≤ Real.exp (-a * R) at hb
  rw [← (OracleTemplate.RobustGradient.stream_groups_preserving Q R n).measureReal_preimage
    hAll.nullMeasurableSet] at hb
  have hblock (ξ : ℕ → Ω) (j : Fin R) :
      B (fun k : Fin n => ξ (j * n + k)) = F (fun k => ξ (j * n + k)) := by
    exact hrecover (fun k => ξ (j * n + k))
  simpa only [Set.preimage, Set.mem_ofPred_eq, hblock] using hb

lemma trialCandidate_prefix_congr (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ ζ : ℕ → Aux p c × p.Ω)
    (heq : ∀ k < max 1 c.probeSteps, ξ k = ζ k) :
    trialCandidate p c H x ξ = trialCandidate p c H x ζ := by
  unfold trialCandidate
  exact congrArg (fun s => s.selected)
    (localProbe_prefix_congr p c H x ξ ζ (max 1 c.probeSteps) (by omega)
      heq (max 1 c.probeSteps) le_rfl)

lemma trial_amplification (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (x : Space p)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (S : Set (Space p)) (hS : MeasurableSet S) (R : ℕ) (a : ℝ)
    (ha : a ≤ (Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : Measure (Aux p c)).prod P0).real {ξ | trialCandidate p c H x ξ ∈ S}) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | ∀ j : Fin R, trialCandidate p c H x
        (fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)) ∉ S} ≤
      Real.exp (-a * R) := by
  let n := max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups
  let : NeZero n := ⟨by dsimp [n]; omega⟩
  have hm := (trialCandidate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  apply finite_prefix_amplification ((auxLaw p c : Measure (Aux p c)).prod P0)
    n (trialCandidate p c H x) hm _ S hS R a ha
  intro ξ ζ heq
  apply trialCandidate_prefix_congr p c H x ξ ζ
  intro k hk
  exact heq k (by dsimp [n]; omega)

lemma detectorChoice_sound (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (R : ℕ) (A : Space p →L[ℝ] Space p)
    (hvalid : ∀ j < R,
      let ζ := fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)
      |trialEstimate p c H x ζ - inner ℝ (trialCandidate p c H x ζ)
        (A (trialCandidate p c H x ζ))| ≤ c.γ / 2)
    (v : Space p) (hv : detectorChoice p c H x ξ R = some v) :
    inner ℝ v (A v) ≤ -3 * c.γ / 2 := by
  obtain ⟨j, hj, hchoice⟩ := detectorChoice_some_origin p c H x ξ R v hv
  have he := hvalid j hj
  unfold trialChoice at hchoice
  split at hchoice
  · rename_i ha
    have hvv := Option.some.inj hchoice
    rw [← hvv]
    exact validation_acceptance_sound ha he
  · contradiction

lemma detectorChoice_good_exists (p : Params) (c : Config) (hγ : 0 ≤ c.γ)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (x : Space p)
    (ξ : ℕ → Aux p c × p.Ω) (R : ℕ) (A : Space p →L[ℝ] Space p)
    (hvalid : ∀ j < R,
      let ζ := fun k => ξ (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k)
      |trialEstimate p c H x ζ - inner ℝ (trialCandidate p c H x ζ)
        (A (trialCandidate p c H x ζ))| ≤ c.γ / 2)
    (hprobe : ∃ j < R, let v := trialCandidate p c H x (fun k => ξ
      (j * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) + k))
      inner ℝ v (A v) ≤ -3 * c.γ) :
    ∃ v, detectorChoice p c H x ξ R = some v ∧ inner ℝ v (A v) ≤ -3 * c.γ / 2 := by
  cases hc : detectorChoice p c H x ξ R with
  | some v => exact ⟨v, rfl, detectorChoice_sound p c H x ξ R A hvalid v hc⟩
  | none =>
    obtain ⟨j, hj, hp⟩ := hprobe
    have hn := (detectorChoice_none_iff p c H x ξ R).mp hc j hj
    have ha := validation_accepts_negative hγ hp (hvalid j hj)
    simp only [trialChoice, ha, ↓reduceIte] at hn
    contradiction

lemma finite_shift_union_probability {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (E : Set (ℕ → Ω)) (hE : MeasurableSet E) (L R : ℕ) (ν : ℝ)
    (he : (Measure.infinitePi fun _ : ℕ => Q).real E ≤ ν) :
    (Measure.infinitePi fun _ : ℕ => Q).real
      {ξ | ∃ j : Fin R, (fun k => ξ (j * L + k)) ∈ E} ≤ R * ν := by
  let P := Measure.infinitePi fun _ : ℕ => Q
  have hshift (m : ℕ) : MeasurePreserving (fun ξ : ℕ → Ω => fun k => ξ (m + k)) P P :=
    measurePreserving_snd.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving Q m)
  have hset : {ξ : ℕ → Ω | ∃ j : Fin R, (fun k => ξ (j * L + k)) ∈ E} =
      ⋃ j : Fin R, (fun ξ : ℕ → Ω => fun k => ξ (j * L + k)) ⁻¹' E := by
    ext ξ
    simp
  rw [hset]
  calc
    P.real (⋃ j : Fin R, (fun ξ : ℕ → Ω => fun k => ξ (j * L + k)) ⁻¹' E) ≤
        ∑ j : Fin R, P.real ((fun ξ : ℕ → Ω => fun k => ξ (j * L + k)) ⁻¹' E) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin R, ν := Finset.sum_le_sum fun j _ => by
      rw [(hshift (j * L)).measureReal_preimage hE.nullMeasurableSet]
      exact he
    _ = R * ν := by simp

lemma detector_failure_probability (p : Params) (c : Config) (hγ : 0 ≤ c.γ)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (x : Space p)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (A : Space p →L[ℝ] Space p) (R : ℕ) (a ν : ℝ)
    (hprobe : a ≤ (Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ)) ≤ -3 * c.γ})
    (hvalid : (Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | c.γ / 2 < |trialEstimate p c H x ξ -
        inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|} ≤ ν) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | ¬ ∃ v, detectorChoice p c H x ξ R = some v ∧
        inner ℝ v (A v) ≤ -3 * c.γ / 2} ≤ Real.exp (-a * R) + R * ν := by
  let Q := (auxLaw p c : Measure (Aux p c)).prod P0
  let P := Measure.infinitePi fun _ : ℕ => Q
  let L := max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups
  let S := {v : Space p | inner ℝ v (A v) ≤ -3 * c.γ}
  let E := {ξ : ℕ → Aux p c × p.Ω | c.γ / 2 < |trialEstimate p c H x ξ -
    inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|}
  let N := {ξ : ℕ → Aux p c × p.Ω | ∀ j : Fin R,
    trialCandidate p c H x (fun k => ξ (j * L + k)) ∉ S}
  let U := {ξ : ℕ → Aux p c × p.Ω | ∃ j : Fin R, (fun k => ξ (j * L + k)) ∈ E}
  have hv := (trialCandidate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have ht := (trialEstimate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (ht.sub (hv.inner (A.continuous.measurable.comp hv))))
  have hS : MeasurableSet S := measurableSet_le
    (measurable_id.inner A.continuous.measurable) measurable_const
  have hn : P.real N ≤ Real.exp (-a * R) := trial_amplification p c H hH x P0 S hS R a hprobe
  have hu : P.real U ≤ R * ν := finite_shift_union_probability Q E hE L R ν hvalid
  have hsub : {ξ | ¬ ∃ v, detectorChoice p c H x ξ R = some v ∧
      inner ℝ v (A v) ≤ -3 * c.γ / 2} ⊆ N ∪ U := by
    intro ξ hbad
    by_cases hU : ξ ∈ U
    · exact Or.inr hU
    · left
      intro j hj
      apply hbad
      apply detectorChoice_good_exists p c hγ H x ξ R A
      · intro i hi
        have hiE : (fun k => ξ (i * L + k)) ∉ E := by
          intro he
          exact hU ⟨⟨i, hi⟩, he⟩
        exact le_of_not_gt hiE
      · exact ⟨j.val, j.isLt, hj⟩
  exact (measureReal_mono hsub).trans ((measureReal_union_le N U).trans (add_le_add hn hu))

lemma detector_false_acceptance_probability (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (x : Space p)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (A : Space p →L[ℝ] Space p) (R : ℕ) (ν : ℝ)
    (hvalid : (Measure.infinitePi fun _ : ℕ =>
      (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | c.γ / 2 < |trialEstimate p c H x ξ -
        inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|} ≤ ν) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | ∃ v, detectorChoice p c H x ξ R = some v ∧
        -3 * c.γ / 2 < inner ℝ v (A v)} ≤ R * ν := by
  let Q := (auxLaw p c : Measure (Aux p c)).prod P0
  let P := Measure.infinitePi fun _ : ℕ => Q
  let L := max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups
  let E := {ξ : ℕ → Aux p c × p.Ω | c.γ / 2 < |trialEstimate p c H x ξ -
    inner ℝ (trialCandidate p c H x ξ) (A (trialCandidate p c H x ξ))|}
  let U := {ξ : ℕ → Aux p c × p.Ω | ∃ j : Fin R, (fun k => ξ (j * L + k)) ∈ E}
  have hv := (trialCandidate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have ht := (trialEstimate_measurable p c H hH).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (ht.sub (hv.inner (A.continuous.measurable.comp hv))))
  have hu : P.real U ≤ R * ν := finite_shift_union_probability Q E hE L R ν hvalid
  apply le_trans (measureReal_mono (s₂ := U) ?_) hu
  rintro ξ ⟨v, hvv, hbad⟩
  by_contra hU
  have hs := detectorChoice_sound p c H x ξ R A (fun i hi => ?_) v hvv
  · exact (not_lt_of_ge hs) hbad
  · have hiE : (fun k => ξ (i * L + k)) ∉ E := by
      intro he
      exact hU ⟨⟨i, hi⟩, he⟩
    exact le_of_not_gt hiE

lemma detectorChoice_none_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (R : ℕ) :
    MeasurableSet {z : Space p × (ℕ → Aux p c × p.Ω) |
      detectorChoice p c H z.1 z.2 R = none} := by
  induction R with
  | zero => simpa only [detectorChoice, Set.ofPred_true] using MeasurableSet.univ
  | succ R ih =>
    let L := max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups
    have hz : Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) =>
        (z.1, fun k => z.2 (R * L + k))) := by
      apply measurable_fst.prodMk
      apply Measurable.of_eval
      intro k
      exact (measurable_pi_apply _).comp measurable_snd
    have ht := (trialEstimate_measurable p c H hH).comp hz
    have heq : {z : Space p × (ℕ → Aux p c × p.Ω) |
        detectorChoice p c H z.1 z.2 (R + 1) = none} =
        {z | detectorChoice p c H z.1 z.2 R = none} ∩
        {z | -2 * c.γ < trialEstimate p c H z.1 (fun k => z.2 (R * L + k))} := by
      ext z
      cases hc : detectorChoice p c H z.1 z.2 R with
      | some v => simp [detectorChoice, hc]
      | none => simp [detectorChoice, hc, trialChoice, L]
    rw [heq]
    exact ih.inter (measurableSet_lt measurable_const ht)

lemma detectorChoice_selected_measurable (p : Params) (c : Config)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hH : Measurable (Function.uncurry H)) (R : ℕ)
    (S : Set (Space p × Space p)) (hS : MeasurableSet S) :
    MeasurableSet {z : Space p × (ℕ → Aux p c × p.Ω) |
      ∃ v, detectorChoice p c H z.1 z.2 R = some v ∧ (z.1, v) ∈ S} := by
  induction R with
  | zero => simp [detectorChoice]
  | succ R ih =>
    let L := max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups
    have hz : Measurable (fun z : Space p × (ℕ → Aux p c × p.Ω) =>
        (z.1, fun k => z.2 (R * L + k))) := by
      apply measurable_fst.prodMk
      apply Measurable.of_eval
      intro k
      exact (measurable_pi_apply _).comp measurable_snd
    have ht := (trialEstimate_measurable p c H hH).comp hz
    have hv := (trialCandidate_measurable p c H hH).comp hz
    have heq : {z : Space p × (ℕ → Aux p c × p.Ω) |
        ∃ v, detectorChoice p c H z.1 z.2 (R + 1) = some v ∧ (z.1, v) ∈ S} =
        {z | ∃ v, detectorChoice p c H z.1 z.2 R = some v ∧ (z.1, v) ∈ S} ∪
        ({z | detectorChoice p c H z.1 z.2 R = none} ∩
        {z | trialEstimate p c H z.1 (fun k => z.2 (R * L + k)) ≤ -2 * c.γ} ∩
        {z | (z.1, trialCandidate p c H z.1 (fun k => z.2 (R * L + k))) ∈ S}) := by
      ext z
      cases hc : detectorChoice p c H z.1 z.2 R with
      | some v => simp [detectorChoice, hc]
      | none =>
        by_cases ha : trialEstimate p c H z.1 (fun k => z.2 (R * L + k)) ≤ -2 * c.γ
        · simp [detectorChoice, hc, trialChoice, L] at ha ⊢
        · simp [detectorChoice, hc, trialChoice, L] at ha ⊢
    rw [heq]
    exact ih.union (((detectorChoice_none_measurable p c H hH R).inter
      (measurableSet_le ht measurable_const)).inter
      (hS.preimage (measurable_fst.prodMk hv)))

lemma probe_repetition_tuning (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    Real.exp (-a * ((max 1 ⌈Real.log (2 / δ) / a⌉₊ : ℕ) : ℝ)) ≤ δ / 2 := by
  have hc : Real.log (2 / δ) / a ≤ ((max 1 ⌈Real.log (2 / δ) / a⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈Real.log (2 / δ) / a⌉₊))
  have hb := (div_le_iff₀ ha).mp hc
  have he := Real.exp_le_exp.mpr (show
      -a * ((max 1 ⌈Real.log (2 / δ) / a⌉₊ : ℕ) : ℝ) ≤ -Real.log (2 / δ) by nlinarith)
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / δ)] at he
  simpa only [inv_div] using he

lemma primitive_curvature_probe_probability (p : Params) (hd : 0 < p.d) (c : Config)
    (x : Space p) (q : ℝ)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (Hmean : Space p →L[ℝ] Space p) (hH : Measurable (H x))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hη : 0 < c.η) (hpq : p.p.HolderConjugate q) (hp2 : p.p ≤ 2)
    (hηM : c.η * (2 * p.L + c.γ) ≤ 1) (hγ : 0 < c.γ) (hσ : 0 ≤ p.σh)
    (hshift : c.shift = p.L + c.γ)
    (hsym : Hmean.toLinearMap.IsSymmetric) (hbound : ‖Hmean‖ ≤ p.L)
    (hi : ∀ v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ v, (∫ ω, H x ω v ∂P0) = Hmean v)
    (hpi : ∀ v, Integrable (fun ω => ‖H x ω v - Hmean v‖ ^ p.p) P0)
    (hb : ∀ v, (∫ ω, ‖H x ω v - Hmean v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (w : Space p) (hw : ‖w‖ = 1) (hbad : inner ℝ w (Hmean w) ≤ -4 * c.γ)
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤ c.η * (max 1 c.probeSteps : ℕ) * c.γ)
    (hsmall : ∀ ell, 0 ≤ ell → ell ≤ 2 * p.L + c.γ →
      ((1 + c.η * ell) ^ p.p + 6 * c.η ^ p.p * p.σh ^ p.p) ^ max 1 c.probeSteps ≤
        (2 * (1 + c.η * ell) ^ max 1 c.probeSteps) ^ p.p)
    (hnoise : (max 1 c.probeSteps : ℕ) * (c.η ^ p.p * p.σh ^ p.p) ≤ (1 / 4 : ℝ) ^ q / 256) :
    (1 / 4 : ℝ) ^ q / 64 ≤
      (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0).real
      {ξ | inner ℝ (trialCandidate p c H x ξ) (Hmean (trialCandidate p c H x ξ)) ≤ -3 * c.γ} := by
  let : Nontrivial (Space p) := ⟨⟨w, 0, by intro he; simp [he] at hw⟩⟩
  let A := (p.L + c.γ) • ContinuousLinearMap.id ℝ (Space p) - Hmean
  have hAsym : A.toLinearMap.IsSymmetric := by
    exact (LinearMap.IsSymmetric.smul (by rfl) LinearMap.IsSymmetric.id).sub hsym
  have hlo (v : Space p) : 0 ≤ inner ℝ (A v) v := by
    have hh := (HeavyTailedCurvatureGeometry.shifted_quadratic_bounds (γ := c.γ) Hmean hbound v).1
    exact (mul_nonneg hγ.le (sq_nonneg ‖v‖)).trans hh
  have hhi (v : Space p) : inner ℝ (A v) v ≤ (2 * p.L + c.γ) * ‖v‖ ^ 2 :=
    (HeavyTailedCurvatureGeometry.shifted_quadratic_bounds Hmean hbound v).2
  obtain ⟨ell, u, hell, hellM, huunit, hu, hnorm⟩ :=
    HeavyTailedCurvatureGeometry.psd_top_eigenpair A hAsym hlo hhi
  have hprob := localProbe_energy_probability p hd c x ell c.γ q H Hmean hH P0
    hη hpq hp2 hell ((mul_le_mul_of_nonneg_left hellM hη.le).trans hηM) hγ hσ
    (fun v => by simpa only [hshift, real_inner_comm] using hlo v)
    (by simpa only [hshift] using hnorm) hi hm hpi hb u
    (by simpa only [hshift] using hu) huunit htune (hsmall ell hell hellM) hnoise
  refine hprob.trans (measureReal_mono ?_)
  intro ξ he
  apply HeavyTailedCurvatureGeometry.energy_implies_negative_curvature Hmean
    (localProbe_selected_norm p hd c H x ξ) hw hnorm hbad
  simpa only [hshift, Set.mem_ofPred_eq, trialCandidate] using he

end LongTails.Proofs.HeavyTailedSospDetection
