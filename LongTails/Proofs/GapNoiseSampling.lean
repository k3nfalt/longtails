import LongTails.Algorithms.GapNoiseSamples
import LongTails.Proofs.GapNoisePastState
import LongTails.Proofs.GapNoiseIteration
import LongTails.Proofs.ProjectedClippedSampling

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.GapNoiseSampling

open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoisePastState

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma trimProjectionSlots_preserving (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (fun ξ : Fin (n + 2) → Ω => fun i : Fin n =>
      ξ ⟨1 + i.val, by omega⟩) (Measure.pi fun _ : Fin (n + 2) => P)
      (Measure.pi fun _ : Fin n => P) := by
  let index : Fin n → Fin (n + 2) := fun i => ⟨1 + i.val, by omega⟩
  have hinj : Function.Injective index := by
    intro i j h
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp [index] at he
    omega
  have hi := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin (n + 2) => P)
    (X := fun _ (x : Ω) => x) (fun _ => measurable_id.aemeasurable)).precomp hinj
  refine ⟨by fun_prop, ?_⟩
  have hh := hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply (index i)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : Fin (n + 2) => P) _).map_eq] using hh

lemma initialSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (batch pilotBatch groups : ℕ) :
    MeasurePreserving (fun ξ : Fin ((groups + 1) * pilotBatch + batch) → Ω =>
      ((fun (i : Fin (groups + 1)) (j : Fin pilotBatch) => ξ ⟨i.val * pilotBatch + j.val, by
        have hi := Nat.mul_le_mul_right pilotBatch (Nat.succ_le_of_lt i.isLt)
        simp only [Nat.succ_mul] at hi
        have hj := j.isLt
        simp only [Nat.add_mul, Nat.one_mul]
        omega⟩),
       (fun j : Fin batch => ξ ⟨(groups + 1) * pilotBatch + j.val, by omega⟩)))
      (Measure.pi fun _ : Fin ((groups + 1) * pilotBatch + batch) => P)
      ((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => P).prod
        (Measure.pi fun _ : Fin batch => P)) :=
  OracleTemplate.RobustGradient.grouped_split_preserving P (groups + 1) pilotBatch batch

lemma stepSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (batch pilotBatch groups : ℕ) :
    MeasurePreserving (fun ξ : Fin ((groups + 1) * pilotBatch + batch + 2) → Ω =>
      ((fun (i : Fin (groups + 1)) (j : Fin pilotBatch) => ξ ⟨1 + (i.val * pilotBatch + j.val), by
        have hi := Nat.mul_le_mul_right pilotBatch (Nat.succ_le_of_lt i.isLt)
        simp only [Nat.succ_mul] at hi
        have hj := j.isLt
        simp only [Nat.add_mul, Nat.one_mul]
        omega⟩),
       (fun j : Fin batch => ξ ⟨1 + ((groups + 1) * pilotBatch + j.val), by omega⟩)))
      (Measure.pi fun _ : Fin ((groups + 1) * pilotBatch + batch + 2) => P)
      ((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => P).prod
        (Measure.pi fun _ : Fin batch => P)) :=
  (initialSamples_preserving P batch pilotBatch groups).comp
    (trimProjectionSlots_preserving P ((groups + 1) * pilotBatch + batch))

lemma trialSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (batch pilotBatch groups steps : ℕ) :
    MeasurePreserving (trialSamples (Ω := Ω) batch pilotBatch groups steps)
      (Measure.pi fun _ : Fin (((groups + 1) * pilotBatch + batch) +
        ((groups + 1) * pilotBatch + batch + 2) * steps) => P)
      (((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => P).prod
        (Measure.pi fun _ : Fin batch => P)).prod
        (Measure.pi fun _ : Fin steps =>
          (Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => P).prod
            (Measure.pi fun _ : Fin batch => P))) := by
  let n := (groups + 1) * pilotBatch + batch
  have hi : MeasurePreserving (initialSamples (Ω := Ω) batch pilotBatch groups)
      (Measure.pi fun _ : Fin n => P)
      ((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => P).prod
        (Measure.pi fun _ : Fin batch => P)) := initialSamples_preserving P batch pilotBatch groups
  have hs : MeasurePreserving (stepSamples (Ω := Ω) batch pilotBatch groups)
      (Measure.pi fun _ : Fin (n + 2) => P)
      ((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => P).prod
        (Measure.pi fun _ : Fin batch => P)) := stepSamples_preserving P batch pilotBatch groups
  convert (hi.prod ((measurePreserving_pi _ _ (fun _ : Fin steps => hs)).comp
    (OracleTemplate.ClippedExtragradient.groupSamples_preserving P (n + 2) steps))).comp
      (OracleTemplate.RobustGradient.finite_split_preserving P n ((n + 2) * steps)) using 1
  funext ξ
  apply Prod.ext
  · rfl
  · funext j
    dsimp only [trialSamples, Function.comp_def, Prod.map]
    apply congrArg (stepSamples batch pilotBatch groups)
    funext i
    congr 1
    apply Fin.ext
    simp [n, Nat.add_assoc]


lemma finCastSamples_preserving (P : Measure Ω) {n m : ℕ} (h : n = m) :
    MeasurePreserving (fun ξ : Fin m → Ω => fun i : Fin n => ξ (Fin.cast h i))
      (Measure.pi fun _ : Fin m => P) (Measure.pi fun _ : Fin n => P) := by
  subst m
  exact MeasurePreserving.id _

lemma trialBlockSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (t : Tuning) (s : ℕ) :
    let ν := (Measure.pi fun _ : Fin (pilotGroups t s + 1) => Measure.pi fun _ : Fin (pilotBatch t s) => P).prod
      (Measure.pi fun _ : Fin (stageBatch t s) => P)
    MeasurePreserving (trialBlockSamples (Ω := Ω) t s) (Measure.pi fun _ : Fin (trialCalls t s) => P)
      (ν.prod (Measure.pi fun _ : Fin (stageSteps t s) => ν)) := by
  unfold trialBlockSamples
  exact (trialSamples_preserving P (stageBatch t s) (pilotBatch t s) (pilotGroups t s) (stageSteps t s)).comp
    (finCastSamples_preserving P _)

lemma stageSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (t : Tuning) (s : ℕ) :
    let ν := (Measure.pi fun _ : Fin (pilotGroups t s + 1) => Measure.pi fun _ : Fin (pilotBatch t s) => P).prod
      (Measure.pi fun _ : Fin (stageBatch t s) => P)
    MeasurePreserving (stageSamples (Ω := Ω) t s) (Measure.pi fun _ : Fin (stageCalls t s) => P)
      (Measure.pi fun _ : Fin (outerGroups t + 1) => ν.prod (Measure.pi fun _ : Fin (stageSteps t s) => ν)) :=
  (measurePreserving_pi _ _ (fun _ : Fin (outerGroups t + 1) => trialBlockSamples_preserving P t s)).comp
    (OracleTemplate.ClippedExtragradient.groupSamples_preserving P (trialCalls t s) (outerGroups t + 1))

lemma measurable_finalSamples (t : Tuning) : Measurable (finalSamples (Ω := Ω) t) := by
  unfold finalSamples
  fun_prop

lemma finalSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (t : Tuning) :
    MeasurePreserving (finalSamples (Ω := Ω) t) (Measure.pi fun _ : Fin (finalCalls t) => P)
      (Measure.pi fun _ : Fin (outerGroups t + 1) => Measure.pi fun _ : Fin (finalBatch t) => P) := by
  have hh := OracleTemplate.RobustGradient.stream_groups_preserving P (outerGroups t + 1) (finalBatch t)
  have hm := measurable_finalSamples (Ω := Ω) t
  refine ⟨hm, ?_⟩
  rw [← (OracleTemplate.StochasticGeneralized.prefix_preserving P (finalCalls t)).map_eq,
    Measure.map_map hm (by fun_prop)]
  convert hh.map_eq using 1
  congr 1
  funext ξ i j
  simp only [Function.comp_def, finalSamples, Nat.mul_comm]

lemma measurable_batch_reply {A : Type*} [MeasurableSpace A] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) {x : A → E} (hx : Measurable x)
    {n : ℕ} {ξ : A → Fin n → Ω} (hξ : Measurable ξ) :
    Measurable (fun a => (1 / (n : ℝ)) • ∑ j, g (x a) (ξ a j)) := by
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro j _
  exact hg.comp (hx.prodMk ((measurable_pi_apply j).comp hξ))

lemma measurable_pilotFromSamples {A : Type*} [MeasurableSpace A]
    (c : StageConfig (E := E)) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    {x : A → E} (hx : Measurable x) (pilotBatch groups : ℕ)
    {ξ : A → Fin (groups + 1) → Fin pilotBatch → Ω} (hξ : Measurable ξ) :
    Measurable (fun a => pilotFromSamples c g (x a) pilotBatch groups (ξ a)) := by
  unfold pilotFromSamples
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  exact (measurable_regularizedReply c).comp (hx.prodMk
    (measurable_batch_reply hg hx ((measurable_pi_apply i).comp hξ)))

set_option maxHeartbeats 800000 in
lemma measurable_sampledInitial (c : StageConfig (E := E)) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ) :
    Measurable (sampledInitial c g batch pilotBatch groups) := by
  have hp : Measurable (fun ξ : StepSamples Ω batch pilotBatch groups =>
      pilotFromSamples c g c.center pilotBatch groups ξ.1) :=
    measurable_pilotFromSamples c hg measurable_const pilotBatch groups measurable_fst
  have hm : Measurable (fun ξ : StepSamples Ω batch pilotBatch groups =>
      (1 / (batch : ℝ)) • ∑ j, g c.center (ξ.2 j)) :=
    measurable_batch_reply hg measurable_const measurable_snd
  have h := (measurable_initialState c).comp (hp.prodMk hm)
  unfold sampledInitial
  exact h

lemma measurable_sampledStep {proj : E → E} (hproj : Measurable proj)
    (c : StageConfig (E := E)) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups : ℕ) :
    Measurable (Function.uncurry (sampledStep proj c g batch pilotBatch groups)) := by
  classical
  have hx : Measurable (fun w : StageState E × StepSamples Ω batch pilotBatch groups =>
      predictor proj w.1) := (measurable_predictor hproj).comp measurable_fst
  unfold sampledStep Function.uncurry
  apply Measurable.ite (measurableSet_permitted c measurable_fst hx)
  · apply measurable_advance proj hproj c measurable_fst hx
    · exact measurable_pilotFromSamples c hg hx pilotBatch groups
        (measurable_fst.comp measurable_snd)
    · exact measurable_batch_reply hg hx (measurable_snd.comp measurable_snd)
  · apply measurable_state_mk <;> fun_prop

lemma measurable_sampledTrialState {proj : E → E} (hproj : Measurable proj)
    (c : StageConfig (E := E)) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups steps : ℕ) :
    Measurable (Function.uncurry (sampledTrialState proj c g batch pilotBatch groups steps)) := by
  unfold sampledTrialState Function.uncurry
  exact (OracleTemplate.ClippedExtragradient.measurable_iterateSamples
    (measurable_sampledStep hproj c hg batch pilotBatch groups) steps).comp
      (((measurable_sampledInitial c hg batch pilotBatch groups).comp measurable_fst).prodMk measurable_snd)

lemma measurable_sampledTrialOutput {proj : E → E} (hproj : Measurable proj)
    (c : StageConfig (E := E)) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups steps : ℕ) :
    Measurable (Function.uncurry (sampledTrialOutput proj c g batch pilotBatch groups steps)) :=
  (measurable_trialOutput c steps).comp (measurable_sampledTrialState hproj c hg batch pilotBatch groups steps)

lemma measurable_pilotFromSamples_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} (hc : Measurable c) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) {x : A → E} (hx : Measurable x)
    (pilotBatch groups : ℕ) {ξ : A → Fin (groups + 1) → Fin pilotBatch → Ω} (hξ : Measurable ξ) :
    Measurable (fun a => pilotFromSamples (c a) g (x a) pilotBatch groups (ξ a)) := by
  unfold pilotFromSamples
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  exact measurable_regularizedReply_of hc hx
    (measurable_batch_reply hg hx ((measurable_pi_apply i).comp hξ))

lemma measurable_sampledInitial_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} (hc : Measurable c) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ)
    {ξ : A → StepSamples Ω batch pilotBatch groups} (hξ : Measurable ξ) :
    Measurable (fun a => sampledInitial (c a) g batch pilotBatch groups (ξ a)) := by
  unfold sampledInitial
  apply measurable_initialState_of hc
  · exact measurable_pilotFromSamples_of hc hg (measurable_config_center.comp hc) pilotBatch groups
      (measurable_fst.comp hξ)
  · exact measurable_batch_reply hg (measurable_config_center.comp hc) (measurable_snd.comp hξ)

lemma measurable_sampledStep_of {A : Type*} [MeasurableSpace A]
    {proj : E → E} (hproj : Measurable proj) {c : A → StageConfig (E := E)} (hc : Measurable c)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ)
    {state : A → StageState E} (hs : Measurable state)
    {ξ : A → StepSamples Ω batch pilotBatch groups} (hξ : Measurable ξ) :
    Measurable (fun a => sampledStep proj (c a) g batch pilotBatch groups (state a) (ξ a)) := by
  classical
  have hx := (measurable_predictor hproj).comp hs
  unfold sampledStep
  apply Measurable.ite (measurableSet_permitted_of hc hs hx)
  · apply measurable_advance_of hproj hc hs hx
    · exact measurable_pilotFromSamples_of hc hg hx pilotBatch groups (measurable_fst.comp hξ)
    · exact measurable_batch_reply hg hx (measurable_snd.comp hξ)
  · apply measurable_state_mk <;> fun_prop

lemma measurable_sampledTrialState_of {A : Type*} [MeasurableSpace A]
    {proj : E → E} (hproj : Measurable proj) {c : A → StageConfig (E := E)} (hc : Measurable c)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups steps : ℕ)
    {initial : A → StepSamples Ω batch pilotBatch groups} (hi : Measurable initial)
    {ξ : A → Fin steps → StepSamples Ω batch pilotBatch groups} (hξ : Measurable ξ) :
    Measurable (fun a => sampledTrialState proj (c a) g batch pilotBatch groups steps (initial a) (ξ a)) := by
  have ha : Measurable (fun w : StageConfig (E := E) × StageState E × StepSamples Ω batch pilotBatch groups =>
      sampledStep proj w.1 g batch pilotBatch groups w.2.1 w.2.2) :=
    measurable_sampledStep_of hproj measurable_fst hg batch pilotBatch groups
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  exact (OracleTemplate.ClippedExtragradient.measurable_iterateSamples_parameter
    (advance := fun c => sampledStep proj c g batch pilotBatch groups) ha steps).comp
    (hc.prodMk ((measurable_sampledInitial_of hc hg batch pilotBatch groups hi).prodMk hξ))

lemma measurable_sampledTrialOutput_of {A : Type*} [MeasurableSpace A]
    {proj : E → E} (hproj : Measurable proj) {c : A → StageConfig (E := E)} (hc : Measurable c)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups steps : ℕ)
    {initial : A → StepSamples Ω batch pilotBatch groups} (hi : Measurable initial)
    {ξ : A → Fin steps → StepSamples Ω batch pilotBatch groups} (hξ : Measurable ξ) :
    Measurable (fun a => sampledTrialOutput proj (c a) g batch pilotBatch groups steps (initial a) (ξ a)) :=
  measurable_trialOutput_of hc (measurable_sampledTrialState_of hproj hc hg batch pilotBatch groups steps hi hξ) steps

lemma measurable_sampledStageOutput_of {A : Type*} [MeasurableSpace A]
    {proj : E → E} (hproj : Measurable proj) {c : A → StageConfig (E := E)} (hc : Measurable c)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups steps repetitions : ℕ)
    {ξ : A → Fin (repetitions + 1) → TrialSamples Ω batch pilotBatch groups steps} (hξ : Measurable ξ) :
    Measurable (fun a => sampledStageOutput proj (c a) g batch pilotBatch groups steps repetitions (ξ a)) := by
  unfold sampledStageOutput
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  exact measurable_sampledTrialOutput_of hproj hc hg batch pilotBatch groups steps
    (measurable_fst.comp ((measurable_pi_apply i).comp hξ))
    (measurable_snd.comp ((measurable_pi_apply i).comp hξ))

lemma measurable_stageSamples (t : Tuning) (s : ℕ) :
    Measurable (stageSamples (Ω := Ω) t s) := by
  unfold stageSamples trialBlockSamples trialSamples stepSamples initialSamples
  fun_prop

lemma measurable_stageBlockOutput_joint {proj : E → E} (hproj : Measurable proj)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × (Fin (stageCalls t s) → Ω) =>
      stageBlockOutput proj t s w.1.1 w.1.2 g w.2) := by
  have hc : Measurable (fun w : (E × E) × (Fin (stageCalls t s) → Ω) =>
      stageConfig t s w.1.1 w.1.2) := by
    unfold stageConfig
    apply measurable_config_mk <;> fun_prop
  exact measurable_sampledStageOutput_of hproj hc hg (stageBatch t s) (pilotBatch t s)
    (pilotGroups t s) (stageSteps t s) (outerGroups t)
    ((measurable_stageSamples t s).comp measurable_snd)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampledStep_mem {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    (g : E → Ω → E) (batch pilotBatch groups : ℕ) (state : StageState E)
    (hs : state.base ∈ X ∧ state.previousQuery ∈ X)
    (ξ : StepSamples Ω batch pilotBatch groups) :
    (sampledStep proj c g batch pilotBatch groups state ξ).base ∈ X ∧
      (sampledStep proj c g batch pilotBatch groups state ξ).previousQuery ∈ X := by
  classical
  by_cases hp : permitted c state (predictor proj state)
  · simp only [sampledStep, advance, hp, ite_true, updatedState]
    exact ⟨hproj.mem _, hproj.mem _⟩
  · simpa only [sampledStep, hp, ite_false] using hs

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampledTrialState_mem {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    (hc : c.center ∈ X) (g : E → Ω → E) (batch pilotBatch groups steps : ℕ)
    (initial : StepSamples Ω batch pilotBatch groups)
    (ξ : Fin steps → StepSamples Ω batch pilotBatch groups) :
    (sampledTrialState proj c g batch pilotBatch groups steps initial ξ).base ∈ X ∧
      (sampledTrialState proj c g batch pilotBatch groups steps initial ξ).previousQuery ∈ X := by
  apply OracleTemplate.ClippedExtragradient.iterateSamples_invariant
    (Inv := fun state => state.base ∈ X ∧ state.previousQuery ∈ X)
    (fun state hs samples => sampledStep_mem hproj c g batch pilotBatch groups state hs samples)
    steps (sampledInitial c g batch pilotBatch groups initial) _ ξ
  exact ⟨hc, hc⟩

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampledStep_active_iff (proj : E → E) (c : StageConfig (E := E))
    (g : E → Ω → E) (batch pilotBatch groups : ℕ) (state : StageState E)
    (ξ : StepSamples Ω batch pilotBatch groups) :
    (sampledStep proj c g batch pilotBatch groups state ξ).active = true ↔
      permitted c state (predictor proj state) := by
  classical
  by_cases hp : permitted c state (predictor proj state) <;>
    simp [sampledStep, advance, hp, updatedState]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampledTrialOutput_mem {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (c : StageConfig (E := E)) (hc : c.center ∈ X) (g : E → Ω → E)
    (batch pilotBatch groups steps : ℕ) (hN : 0 < steps)
    (initial : StepSamples Ω batch pilotBatch groups) (ξ : Fin steps → StepSamples Ω batch pilotBatch groups) :
    sampledTrialOutput proj c g batch pilotBatch groups steps initial ξ ∈ X := by
  classical
  let advance := sampledStep proj c g batch pilotBatch groups
  let start := sampledInitial c g batch pilotBatch groups initial
  let finish := sampledTrialState proj c g batch pilotBatch groups steps initial ξ
  by_cases hactive : finish.active = true
  · have ha (state : StageState E) (samples : StepSamples Ω batch pilotBatch groups)
        (h : (advance state samples).active = true) : state.active = true :=
      ((sampledStep_active_iff proj c g batch pilotBatch groups state samples).mp h).1
    have ht (state : StageState E) (samples : StepSamples Ω batch pilotBatch groups)
        (h : (advance state samples).active = true) :
        (advance state samples).total = state.total + predictor proj state := by
      have hp := (sampledStep_active_iff proj c g batch pilotBatch groups state samples).mp h
      simp only [advance, sampledStep, hp, ite_true, LongTails.Algorithms.GapNoisePastExtragradient.advance, updatedState]
    have htotal := GapNoiseIteration.active_total_trace (advance := advance)
      (active := fun state => state.active = true) (total := StageState.total)
      (point := predictor proj) ha ht steps start ξ hactive
    have hzero : start.total = 0 := rfl
    rw [hzero, zero_add] at htotal
    have hpoints := GapNoiseIteration.pointTrace_mem advance (predictor proj) (fun _ => hproj.mem _) steps start ξ
    have hw : (∑ _i : Fin steps, (1 / (steps : ℝ))) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_one_div_cancel (Nat.cast_ne_zero.mpr hN.ne')
    have hm := hX.sum_mem (fun (_i : Fin steps) _ => (by positivity : (0 : ℝ) ≤ 1 / steps)) hw
      (fun i _ => hpoints i)
    change (if finish.active then (1 / (steps : ℝ)) • finish.total else c.center) ∈ X
    simp only [hactive, ite_true]
    change (1 / (steps : ℝ)) • (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps start ξ).total ∈ X
    rw [htotal, Finset.smul_sum]
    exact hm
  · change (if finish.active then (1 / (steps : ℝ)) • finish.total else c.center) ∈ X
    simpa only [hactive, Bool.false_eq_true, ite_false] using hc

lemma measurable_sampledStageOutput {proj : E → E} (hproj : Measurable proj)
    (c : StageConfig (E := E)) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups steps repetitions : ℕ) :
    Measurable (sampledStageOutput proj c g batch pilotBatch groups steps repetitions) := by
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  exact Measurable.of_eval (fun i =>
    (measurable_sampledTrialOutput hproj c hg batch pilotBatch groups steps).comp (measurable_pi_apply i))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampledStageOutput_mem {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (c : StageConfig (E := E)) (hc : c.center ∈ X) (g : E → Ω → E)
    (batch pilotBatch groups steps repetitions : ℕ) (hN : 0 < steps)
    (ξ : Fin (repetitions + 1) → TrialSamples Ω batch pilotBatch groups steps) :
    sampledStageOutput proj c g batch pilotBatch groups steps repetitions ξ ∈ X := by
  unfold sampledStageOutput OracleTemplate.MultiplicativeRobustEstimator.medoid
  exact sampledTrialOutput_mem hproj hX c hc g batch pilotBatch groups steps hN _ _

lemma measurable_sampledFinalEstimate_of {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : Tuning)
    {x : A → E} (hx : Measurable x)
    {ξ : A → Fin (outerGroups t + 1) → Fin (finalBatch t) → Ω} (hξ : Measurable ξ) :
    Measurable (fun a => sampledFinalEstimate t (x a) g (ξ a)) := by
  unfold sampledFinalEstimate
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  exact measurable_batch_reply hg hx ((measurable_pi_apply i).comp hξ)

lemma measurable_finalBlockEstimate_joint {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (t : Tuning) : Measurable (fun w : E × (Fin (finalCalls t) → Ω) => finalBlockEstimate t w.1 g w.2) :=
  measurable_sampledFinalEstimate_of hg t measurable_fst ((measurable_finalSamples t).comp measurable_snd)

lemma measurable_finalBlockOutput_joint {proj : E → E} (hproj : Measurable proj)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : Tuning) :
    Measurable (fun w : (E × E) × (Fin (finalCalls t) → Ω) => finalBlockOutput proj t w.1.1 w.1.2 g w.2) := by
  have he : Measurable (fun w : (E × E) × (Fin (finalCalls t) → Ω) =>
      finalBlockEstimate t w.1.2 g w.2) := (measurable_finalBlockEstimate_joint hg t).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  unfold finalBlockOutput OracleTemplate.ClippedExtragradient.regularizedReply
  fun_prop

lemma measurable_phaseReply {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (phaseReply P t g n)) := by
  have hs := OracleTemplate.ClippedExtragradient.measurable_guarded_block (Ω := Ω) (stageCalls t)
    (fun s (a : E × E) ξ => stageBlockOutput P t s a.1 a.2 g ξ) Prod.snd measurable_snd
    (measurable_stageBlockOutput_joint hP hg t) n
  have hf : Measurable (fun w : OracleTemplate.ProjectedClippedExtragradient.ProcessState E × (Fin n → Ω) =>
      if hn : n = finalCalls t then finalBlockOutput P t w.1.2.1 w.1.2.2 g
        (fun i => w.2 (Fin.cast hn.symm i)) else w.1.2.2) := by
    by_cases hn : n = finalCalls t
    · subst n
      simpa only [dite_true, Fin.cast_refl, id_eq, Function.comp_def] using
        (measurable_finalBlockOutput_joint hP hg t).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    · simp only [hn, dite_false]
      fun_prop
  exact hs.ite (measurableSet_lt (by fun_prop) measurable_const) hf

lemma measurable_phaseNext {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (phaseNext P t g n)) := by
  classical
  have hw := measurable_phaseReply hP hg t n
  have ha : Measurable (fun w : OracleTemplate.ProjectedClippedExtragradient.ProcessState E × (Fin n → Ω) => w.1.2.1) := by fun_prop
  have hx : Measurable (fun w : OracleTemplate.ProjectedClippedExtragradient.ProcessState E × (Fin n → Ω) =>
      if w.1.1 + 1 < stages t then (1 / 2 : ℝ) • (w.1.2.1 + phaseReply P t g n w.1 w.2)
      else w.1.2.1) := ((ha.add hw).const_smul (1 / 2 : ℝ)).ite
    (measurableSet_lt (show Measurable (fun w : OracleTemplate.ProjectedClippedExtragradient.ProcessState E × (Fin n → Ω) => w.1.1 + 1) by fun_prop)
      (measurable_const (a := stages t))) ha
  exact (by fun_prop : Measurable (fun w : OracleTemplate.ProjectedClippedExtragradient.ProcessState E × (Fin n → Ω) => w.1.1 + 1)).prodMk
    (hx.prodMk hw)

end LongTails.Proofs.GapNoiseSampling
