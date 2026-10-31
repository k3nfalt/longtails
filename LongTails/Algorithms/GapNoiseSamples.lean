import LongTails.Algorithms.GapNoisePastExtragradient

namespace LongTails.Algorithms.GapNoisePastExtragradient

open OracleTemplate

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev StepSamples (Ω : Type) (batch pilotBatch groups : ℕ) :=
  (Fin (groups + 1) → Fin pilotBatch → Ω) × (Fin batch → Ω)

noncomputable def pilotFromSamples (c : StageConfig (E := E)) (g : E → Ω → E) (x : E)
    (pilotBatch groups : ℕ) (ξ : Fin (groups + 1) → Fin pilotBatch → Ω) : E :=
  MultiplicativeRobustEstimator.medoid (fun i => regularizedReply c x
    ((1 / (pilotBatch : ℝ)) • ∑ j, g x (ξ i j)))

noncomputable def sampledInitial (c : StageConfig (E := E)) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (ξ : StepSamples Ω batch pilotBatch groups) : StageState E :=
  initialState c (pilotFromSamples c g c.center pilotBatch groups ξ.1)
    ((1 / (batch : ℝ)) • ∑ j, g c.center (ξ.2 j))

noncomputable def sampledStep (proj : E → E) (c : StageConfig (E := E)) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E)
    (ξ : StepSamples Ω batch pilotBatch groups) : StageState E := by
  classical
  let x := predictor proj state
  exact if permitted c state x then
    advance proj c state x (pilotFromSamples c g x pilotBatch groups ξ.1)
      ((1 / (batch : ℝ)) • ∑ j, g x (ξ.2 j))
  else { state with active := false }

noncomputable def sampledTrialState (proj : E → E) (c : StageConfig (E := E)) (g : E → Ω → E)
    (batch pilotBatch groups steps : ℕ) (initial : StepSamples Ω batch pilotBatch groups)
    (ξ : Fin steps → StepSamples Ω batch pilotBatch groups) : StageState E :=
  ContinuizedSimilarQuasar.iterateSamples (sampledStep proj c g batch pilotBatch groups)
    steps (sampledInitial c g batch pilotBatch groups initial) ξ

noncomputable def sampledTrialOutput (proj : E → E) (c : StageConfig (E := E)) (g : E → Ω → E)
    (batch pilotBatch groups steps : ℕ) (initial : StepSamples Ω batch pilotBatch groups)
    (ξ : Fin steps → StepSamples Ω batch pilotBatch groups) : E :=
  trialOutput c steps (sampledTrialState proj c g batch pilotBatch groups steps initial ξ)

abbrev TrialSamples (Ω : Type) (batch pilotBatch groups steps : ℕ) :=
  StepSamples Ω batch pilotBatch groups × (Fin steps → StepSamples Ω batch pilotBatch groups)

noncomputable def sampledStageOutput (proj : E → E) (c : StageConfig (E := E)) (g : E → Ω → E)
    (batch pilotBatch groups steps repetitions : ℕ)
    (ξ : Fin (repetitions + 1) → TrialSamples Ω batch pilotBatch groups steps) : E :=
  MultiplicativeRobustEstimator.medoid (fun i =>
    sampledTrialOutput proj c g batch pilotBatch groups steps (ξ i).1 (ξ i).2)

def initialSamples (batch pilotBatch groups : ℕ)
    (ξ : Fin ((groups + 1) * pilotBatch + batch) → Ω) : StepSamples Ω batch pilotBatch groups :=
  ((fun i j => ξ ⟨i.val * pilotBatch + j.val, by
      have hi := Nat.mul_le_mul_right pilotBatch (Nat.succ_le_of_lt i.isLt)
      simp only [Nat.succ_mul] at hi
      have hj := j.isLt
      simp only [Nat.add_mul, Nat.one_mul]
      omega⟩),
   (fun j => ξ ⟨(groups + 1) * pilotBatch + j.val, by omega⟩))

def stepSamples (batch pilotBatch groups : ℕ)
    (ξ : Fin ((groups + 1) * pilotBatch + batch + 2) → Ω) : StepSamples Ω batch pilotBatch groups :=
  initialSamples batch pilotBatch groups (fun i => ξ ⟨1 + i.val, by omega⟩)

def trialSamples (batch pilotBatch groups steps : ℕ)
    (ξ : Fin (((groups + 1) * pilotBatch + batch) +
      ((groups + 1) * pilotBatch + batch + 2) * steps) → Ω) : TrialSamples Ω batch pilotBatch groups steps :=
  (initialSamples batch pilotBatch groups (fun i => ξ ⟨i.val, by omega⟩),
   fun j => stepSamples batch pilotBatch groups (fun i =>
     ξ ⟨((groups + 1) * pilotBatch + batch) +
       ((groups + 1) * pilotBatch + batch + 2) * j.val + i.val, by
       have hj := Nat.mul_le_mul_left ((groups + 1) * pilotBatch + batch + 2)
         (Nat.succ_le_of_lt j.isLt)
       rw [Nat.mul_succ] at hj
       have hi := i.isLt
       omega⟩))

noncomputable def trialBlockSamples (t : Tuning) (s : ℕ)
    (ξ : Fin (trialCalls t s) → Ω) :
    TrialSamples Ω (stageBatch t s) (pilotBatch t s) (pilotGroups t s) (stageSteps t s) :=
  let h : ((pilotGroups t s + 1) * pilotBatch t s + stageBatch t s) +
      ((pilotGroups t s + 1) * pilotBatch t s + stageBatch t s + 2) * stageSteps t s = trialCalls t s := by
    unfold trialCalls
    ring
  trialSamples (stageBatch t s) (pilotBatch t s) (pilotGroups t s) (stageSteps t s)
    (fun i => ξ (Fin.cast h i))

noncomputable def stageSamples (t : Tuning) (s : ℕ) (ξ : Fin (stageCalls t s) → Ω) :
    Fin (outerGroups t + 1) →
      TrialSamples Ω (stageBatch t s) (pilotBatch t s) (pilotGroups t s) (stageSteps t s) :=
  fun j => trialBlockSamples t s (fun i => ξ ⟨trialCalls t s * j.val + i.val, by
    have hj := Nat.mul_le_mul_left (trialCalls t s) (Nat.succ_le_of_lt j.isLt)
    rw [Nat.mul_succ] at hj
    have hi := i.isLt
    unfold stageCalls
    omega⟩)

noncomputable def stageBlockOutput (proj : E → E) (t : Tuning) (s : ℕ)
    (anchor center : E) (g : E → Ω → E) (ξ : Fin (stageCalls t s) → Ω) : E :=
  sampledStageOutput proj (stageConfig t s anchor center) g (stageBatch t s) (pilotBatch t s)
    (pilotGroups t s) (stageSteps t s) (outerGroups t) (stageSamples t s ξ)

noncomputable def sampledFinalEstimate (t : Tuning) (x : E) (g : E → Ω → E)
    (ξ : Fin (outerGroups t + 1) → Fin (finalBatch t) → Ω) : E :=
  MultiplicativeRobustEstimator.medoid (fun i => (1 / (finalBatch t : ℝ)) • ∑ j, g x (ξ i j))

noncomputable def finalSamples (t : Tuning) (ξ : Fin (finalCalls t) → Ω) :
    Fin (outerGroups t + 1) → Fin (finalBatch t) → Ω :=
  fun i j => ξ ⟨finalBatch t * i.val + j.val, by
    have hi := Nat.mul_le_mul_left (finalBatch t) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at hi
    have hj := j.isLt
    unfold finalCalls
    omega⟩

noncomputable def finalBlockEstimate (t : Tuning) (x : E) (g : E → Ω → E)
    (ξ : Fin (finalCalls t) → Ω) : E :=
  sampledFinalEstimate t x g (finalSamples t ξ)

noncomputable def finalBlockOutput (proj : E → E) (t : Tuning) (anchor x : E) (g : E → Ω → E)
    (ξ : Fin (finalCalls t) → Ω) : E :=
  proj (x - ProjectedClippedExtragradient.finalStepSize (geometry t) •
    ClippedExtragradient.regularizedReply
      (ProjectedClippedExtragradient.regularization (geometry t) (stages t - 1)) anchor x
        (finalBlockEstimate t x g ξ))

noncomputable def phaseCost (t : Tuning) (state : ProjectedClippedExtragradient.ProcessState E) : ℕ :=
  if state.1 < stages t then stageCalls t state.1 else finalCalls t

noncomputable def phaseReply {Ω : Type} (P : E → E) (t : Tuning) (g : E → Ω → E)
    (n : ℕ) (state : ProjectedClippedExtragradient.ProcessState E) (ξ : Fin n → Ω) : E :=
  if state.1 < stages t then
    if hn : n = stageCalls t state.1 then
      stageBlockOutput P t state.1 state.2.1 state.2.2 g (fun i => ξ (Fin.cast hn.symm i))
    else state.2.2
  else
    if hn : n = finalCalls t then
      finalBlockOutput P t state.2.1 state.2.2 g (fun i => ξ (Fin.cast hn.symm i))
    else state.2.2

noncomputable def phaseNext {Ω : Type} (P : E → E) (t : Tuning) (g : E → Ω → E)
    (n : ℕ) (state : ProjectedClippedExtragradient.ProcessState E) (ξ : Fin n → Ω) : ProjectedClippedExtragradient.ProcessState E :=
  let w := phaseReply P t g n state ξ
  (state.1 + 1, (if state.1 + 1 < stages t then (1 / 2 : ℝ) • (state.2.1 + w) else state.2.1), w)

end LongTails.Algorithms.GapNoisePastExtragradient
