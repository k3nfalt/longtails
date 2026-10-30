import LongTails.Algorithms.GapNoiseSamples
import LongTails.Proofs.ProjectedClippedExecution

namespace LongTails.Proofs.GapNoiseExecution

open OracleTemplate
open LongTails.Algorithms.GapNoisePastExtragradient
open OracleTemplate.ProjectedClippedExtragradient (channelReply sampled_meanPlan)

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sampled_pilotPlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (c : StageConfig (E := E)) (x : E) (batch groups call : ℕ) :
    QueryPlan.sampledEval (channelReply proj g) ξ (pilotPlan c x batch groups) call =
      pilotFromSamples c g x batch groups
        (fun j i => ξ (call + batch * j.val + i.val)) := by
  rw [pilotPlan, QueryPlan.sampledEval_map, QueryPlan.sampledEval_traverse]
  unfold pilotFromSamples
  congr 1
  funext j
  rw [List.getElem?_ofFn]
  simp only [j.isLt, dite_true, Option.getD_some, QueryPlan.sampledEval_map,
    sampled_meanPlan]

lemma sampled_initialPlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (c : StageConfig (E := E)) (batch pilotBatch groups call : ℕ) :
    QueryPlan.sampledEval (channelReply proj g) ξ (initialPlan c batch pilotBatch groups) call =
      sampledInitial c g batch pilotBatch groups
        ((fun j i => ξ (call + pilotBatch * j.val + i.val)),
         (fun i => ξ (call + pilotBatch * (groups + 1) + i.val))) := by
  rw [initialPlan, QueryPlan.sampledEval_bind, sampled_pilotPlan,
    QueryPlan.sampledEval_map, sampled_meanPlan]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sampled_idlePlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (center : E) (state : StageState E) (calls call : ℕ) :
    QueryPlan.sampledEval (channelReply proj g) ξ (idlePlan center state calls) call = state := by
  induction calls generalizing call with
  | zero => rfl
  | succ calls ih => exact ih (call + 1)

lemma sampled_stepPlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (c : StageConfig (E := E)) (batch pilotBatch groups call : ℕ) (state : StageState E) :
    QueryPlan.sampledEval (channelReply proj g) ξ (stepPlan c batch pilotBatch groups state) call =
      sampledStep proj c g batch pilotBatch groups state
        ((fun j i => ξ (call + 1 + pilotBatch * j.val + i.val)),
         (fun i => ξ (call + 1 + pilotBatch * (groups + 1) + i.val))) := by
  classical
  simp only [stepPlan, QueryPlan.sampledEval, channelReply, Fin.isValue,
    Fin.one_eq_zero_iff, show ¬(2 = 1) by decide, ite_false]
  change QueryPlan.sampledEval _ _ (if permitted c state (predictor proj state) then _ else _) _ = _
  by_cases hp : permitted c state (predictor proj state)
  · simp only [ite_true, QueryPlan.sampledEval_bind, sampled_pilotPlan,
      sampled_meanPlan, QueryPlan.sampledEval, channelReply, Fin.isValue,
      Fin.one_eq_zero_iff, show ¬(2 = 1) by decide, ite_false, sampledStep, advance, hp, ite_true]
    rfl
  · simp only [hp, ite_false, sampled_idlePlan, sampledStep]

lemma sampled_repeatPlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (c : StageConfig (E := E)) (batch pilotBatch groups steps call : ℕ) (state : StageState E) :
    QueryPlan.sampledEval (channelReply proj g) ξ
      (repeatPlan (stepPlan c batch pilotBatch groups) steps state) call =
      ContinuizedSimilarQuasar.iterateSamples (sampledStep proj c g batch pilotBatch groups)
        steps state (fun j =>
          ((fun i k => ξ (call + (((1 + batch) + pilotBatch * (groups + 1)) + 1) * j.val +
              1 + pilotBatch * i.val + k.val)),
           (fun i => ξ (call + (((1 + batch) + pilotBatch * (groups + 1)) + 1) * j.val +
              1 + pilotBatch * (groups + 1) + i.val)))) := by
  induction steps generalizing state call with
  | zero => rfl
  | succ steps ih =>
    rw [repeatPlan, QueryPlan.sampledEval_bind, ih]
    simp only [ContinuizedSimilarQuasar.iterateSamples, Fin.val_zero, mul_zero, add_zero,
      Fin.val_succ, sampled_stepPlan]
    congr 1
    funext j
    apply Prod.ext
    · funext i k
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · funext i
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma sampled_trialPlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (c : StageConfig (E := E)) (batch pilotBatch groups steps call : ℕ) :
    QueryPlan.sampledEval (channelReply proj g) ξ (trialPlan c batch pilotBatch groups steps) call =
      sampledTrialOutput proj c g batch pilotBatch groups steps
        ((fun j i => ξ (call + pilotBatch * j.val + i.val)),
         (fun i => ξ (call + pilotBatch * (groups + 1) + i.val)))
        (fun j =>
          ((fun i k => ξ (call + (batch + pilotBatch * (groups + 1)) +
              (((1 + batch) + pilotBatch * (groups + 1)) + 1) * j.val +
              1 + pilotBatch * i.val + k.val)),
           (fun i => ξ (call + (batch + pilotBatch * (groups + 1)) +
              (((1 + batch) + pilotBatch * (groups + 1)) + 1) * j.val +
              1 + pilotBatch * (groups + 1) + i.val)))) := by
  rw [trialPlan, QueryPlan.sampledEval_bind, sampled_initialPlan,
    QueryPlan.sampledEval_map, sampled_repeatPlan]
  rfl

lemma sampled_stagePlan (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (t : Tuning) (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval (channelReply proj g) ξ (stagePlan t s anchor center) call =
      MultiplicativeRobustEstimator.medoid (fun i : Fin (outerGroups t + 1) =>
        QueryPlan.sampledEval (channelReply proj g) ξ
          (trialPlan (stageConfig t s anchor center) (stageBatch t s) (pilotBatch t s)
            (pilotGroups t s) (stageSteps t s)) (call + trialCalls t s * i.val)) := by
  unfold stagePlan stageCalls trialCalls
  rw [QueryPlan.sampledEval_map, QueryPlan.sampledEval_traverse]
  congr 1
  funext i
  rw [List.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some]

lemma sampled_trialPlan_samples (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (c : StageConfig (E := E)) (batch pilotBatch groups steps call : ℕ) :
    QueryPlan.sampledEval (channelReply proj g) ξ (trialPlan c batch pilotBatch groups steps) call =
      Function.uncurry (sampledTrialOutput proj c g batch pilotBatch groups steps)
        (trialSamples batch pilotBatch groups steps (fun i => ξ (call + i.val))) := by
  rw [sampled_trialPlan]
  simp only [Function.uncurry, trialSamples, stepSamples, initialSamples,
    Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  congr 1
  funext j
  apply Prod.ext
  · funext i k
    ring
  · funext i
    ring

lemma sampled_trialBlock (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (t : Tuning) (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval (channelReply proj g) ξ
      (trialPlan (stageConfig t s anchor center) (stageBatch t s) (pilotBatch t s)
        (pilotGroups t s) (stageSteps t s)) call =
      Function.uncurry (sampledTrialOutput proj (stageConfig t s anchor center) g
        (stageBatch t s) (pilotBatch t s) (pilotGroups t s) (stageSteps t s))
        (trialBlockSamples t s (fun i => ξ (call + i.val))) := by
  rw [sampled_trialPlan_samples]
  rfl

lemma sampled_stagePlan_samples (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (t : Tuning) (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval (channelReply proj g) ξ (stagePlan t s anchor center) call =
      sampledStageOutput proj (stageConfig t s anchor center) g (stageBatch t s)
        (pilotBatch t s) (pilotGroups t s) (stageSteps t s) (outerGroups t)
        (stageSamples t s (fun i => ξ (call + i.val))) := by
  rw [sampled_stagePlan]
  unfold sampledStageOutput
  congr 1
  funext i
  rw [sampled_trialBlock]
  simp only [stageSamples, Function.uncurry, Nat.add_assoc]

lemma sampled_finalPlan_samples (proj : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (t : Tuning) (call : ℕ) (anchor x : E) :
    QueryPlan.sampledEval (channelReply proj g) ξ (finalPlan t anchor x) call =
      finalBlockOutput proj t anchor x g (fun i => ξ (call + i.val)) := by
  erw [finalPlan, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_traverse]
  simp only [QueryPlan.sampledEval, channelReply, Fin.isValue, Fin.one_eq_zero_iff,
    show ¬(2 = 1) by decide, ite_false]
  unfold finalBlockOutput finalBlockEstimate sampledFinalEstimate finalSamples
  apply congrArg (fun estimate => proj (x - ProjectedClippedExtragradient.finalStepSize (geometry t) •
    ClippedExtragradient.regularizedReply
      (ProjectedClippedExtragradient.regularization (geometry t) (stages t - 1)) anchor x estimate))
  apply congrArg MultiplicativeRobustEstimator.medoid
  funext i
  rw [List.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some, sampled_meanPlan, Nat.add_assoc]


lemma sampled_run_trace (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s n call : ℕ) (anchor center : E) (hindex : s + n = stages t) :
    QueryPlan.sampledEval (channelReply P g) ξ (runPlan t s n anchor center) call =
      (StochasticGeneralized.blockTrace (phaseCost t) (phaseNext P t g) (s, anchor, center)
        (fun j => ξ (call + j)) (n + 1)).1.2.2 := by
  induction n generalizing s call anchor center with
  | zero =>
    have hs : s = stages t := by omega
    erw [runPlan, sampled_finalPlan_samples, StochasticGeneralized.blockTrace_start_succ,
      StochasticGeneralized.blockTrace_zero]
    simp only [phaseNext, phaseReply, phaseCost, hs, lt_self_iff_false, ite_false]
    rfl
  | succ n ih =>
    have hs : s < stages t := by omega
    conv_rhs => rw [StochasticGeneralized.blockTrace_start_succ]
    erw [runPlan, QueryPlan.sampledEval_bind, sampled_stagePlan_samples, ih (s + 1) _ _ _ (by omega)]
    simp only [phaseNext, phaseReply, phaseCost, hs, ite_true, Nat.add_assoc]
    by_cases hn : n = 0
    · have hnext : ¬s + 1 < stages t := by omega
      simp only [hn, ite_true, hnext, ite_false]
      rfl
    · have hnext : s + 1 < stages t := by omega
      simp only [hn, ite_false, hnext, ite_true]
      rfl

lemma execute_trace [MeasurableSpace Ω] (law : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (P : E → E) (g : E → Ω → E) (t : Tuning) (x0 : E) (K : ℕ)
    (hK : runCalls t 0 (stages t) ≤ K) (seed : Unit) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ q ω => channelReply P g q ω }
      (algorithm t x0) (fun _ => K) seed ξ =
      (StochasticGeneralized.blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0)
        ξ (stages t + 1)).1.2.2 := by
  have hh := QueryPlan.execute_sampledChannels_of_le (channelReply P g) (0, x0) x0
    (runPlan t 0 (stages t) x0 x0)
    { Seed := fun _ => Ω, law := law, answer := fun _ q ω => channelReply P g q ω }
    (fun _ => rfl) (fun _ => K) (fun _ => hK) (fun _ _ _ => rfl) seed ξ
  change execute { Seed := fun _ => Ω, law := law, answer := fun _ q ω => channelReply P g q ω }
    (algorithm t x0) (fun _ => K) seed ξ = _ at hh
  rw [hh]
  simp only [cast_eq]
  rw [sampled_run_trace P g ξ t 0 (stages t) 0 x0 x0 (by omega)]
  simp only [Nat.zero_add]

end LongTails.Proofs.GapNoiseExecution
