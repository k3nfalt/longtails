import LongTails.Algorithms.ProjectedClippedExtragradient
import LongTails.Proofs.AdaptiveIID
import Mathlib.Data.List.GetD
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.EnergyHessianExecution

namespace OracleTemplate.QueryPlan

open LongTails.Algorithms.EnergyHessianReuse
open LongTails.Proofs.EnergyHessianExecution (length_update)

variable {Q R U Ω : Type} {n : ℕ}

lemma sampledEval_update (g : (Fin n × Q) → Ω → R) (ξ : ℕ → Ω)
    (q0 : Fin n × Q) (s : Σ k, QueryPlan (Fin n × Q) R U k) (call : ℕ) :
    sampledEval g ξ (update s (g (query q0 s) (ξ call))).2 (call + 1) =
      sampledEval g ξ s.2 call := by
  obtain ⟨k, plan⟩ := s
  cases plan <;> rfl

lemma execute_sampledChannels_of_le (g : (Fin n × Q) → Ω → R)
    (q0 : Fin n × Q) (u0 : U) {K : ℕ} (plan : QueryPlan (Fin n × Q) R U K)
    (O : Oracle Q R n) (hSeed : ∀ k, O.Seed k = Ω)
    (budget : Fin n → ℕ) (hb : ∀ i, K ≤ budget i)
    (hO : ∀ k q ω, O.answer k q ω = g q (cast (hSeed k.length) ω))
    (seed : (channelAlgorithm q0 u0 plan).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (channelAlgorithm q0 u0 plan) budget seed ξ =
      sampledEval g (fun k => cast (hSeed k) (ξ k)) plan 0 := by
  let ζ := fun k => cast (hSeed k) (ξ k)
  let state : ℕ → (Σ k, QueryPlan (Fin n × Q) R U k) :=
    Nat.rec ⟨K, plan⟩ (fun k s => update s (g (query q0 s) (ζ k)))
  have hstep (k : ℕ) : state (k + 1) = update (state k) (g (query q0 (state k)) (ζ k)) := rfl
  let remaining : ℕ → Fin n → ℕ :=
    Nat.rec budget (fun k b => Function.update b (query q0 (state k)).1
      (b (query q0 (state k)).1 - 1))
  have hremaining (k : ℕ) : remaining (k + 1) =
      Function.update (remaining k) (query q0 (state k)).1
        (remaining k (query q0 (state k)).1 - 1) := rfl
  have hcover (k : ℕ) (i : Fin n) : K - k ≤ remaining k i := by
    induction k with
    | zero => exact hb i
    | succ k ih =>
      rw [hremaining]
      by_cases hi : i = (query q0 (state k)).1
      · rw [hi, Function.update_self]
        have := ih
        rw [hi] at this
        omega
      · rw [Function.update_of_ne hi]
        omega
  have hlength (k : ℕ) : (state k).1 = K - k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, length_update (fun q => g q (ζ k)) q0, ih]; omega
  have heval (k : ℕ) : sampledEval g ζ (state k).2 k = sampledEval g ζ plan 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, sampledEval_update, ih]
  apply execute_eq_of_safe_prefix O (channelAlgorithm q0 u0 plan) budget seed ξ
    state remaining K (sampledEval g ζ plan 0)
  · rfl
  · intro k
    change state (k.length + 1) = update (state k.length)
      (O.answer k (query q0 (state k.length)) (ξ k.length))
    rw [hO]
  · rfl
  · exact hremaining
  · intro k hk
    exact (Nat.sub_pos_of_lt hk).trans_le (hcover k _)
  · intro k hk
    change output u0 (state k) = _
    have hz : (state k).1 = 0 := by rw [hlength]; omega
    have hout : output u0 (state k) = sampledEval g ζ (state k).2 k := by
      generalize state k = st at hz ⊢
      obtain ⟨j, pl⟩ := st
      cases pl with
      | done value => rfl
      | ask q rest => simp at hz
    rw [hout, heval]
  · exact (hb q0.1).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (budget i)) (Finset.mem_univ q0.1))

end OracleTemplate.QueryPlan

open scoped BigOperators

namespace OracleTemplate.ProjectedClippedExtragradient

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def channelReply (P : E → E) (g : E → Ω → E) (q : Fin 2 × E) (ω : Ω) : E :=
  if q.1 = 0 then g q.2 ω else P q.2

omit [NormedSpace ℝ E] in
lemma sampled_sumPlan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (x : E) (n call : ℕ) :
    QueryPlan.sampledEval (channelReply P g) ξ (sumPlan x n) call =
      ∑ i : Fin n, g x (ξ (call + i.val)) := by
  induction n generalizing call with
  | zero => simp [sumPlan, QueryPlan.sampledEval]
  | succ n ih =>
    simp only [sumPlan, QueryPlan.sampledEval, QueryPlan.sampledEval_map, ih,
      channelReply, Fin.sum_univ_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega

lemma sampled_meanPlan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (x : E) (n call : ℕ) :
    QueryPlan.sampledEval (channelReply P g) ξ (meanPlan n x) call =
      (1 / (n : ℝ)) • ∑ i : Fin n, g x (ξ (call + i.val)) := by
  rw [meanPlan, QueryPlan.sampledEval_map, sampled_sumPlan]

lemma sampled_stepPlan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s call : ℕ) (anchor center x : E) :
    QueryPlan.sampledEval (channelReply P g) ξ (stepPlan t s anchor center x) call =
      batchStep P (batchSize t s) t.L1 (localScale t s) (radius t s) (regularization t s)
        anchor center g x
        ((fun i => ξ (call + i.val)), (fun i => ξ (call + batchSize t s + 1 + i.val))) := by
  simp only [stepPlan, QueryPlan.sampledEval_bind, sampled_meanPlan, QueryPlan.sampledEval,
    channelReply, Fin.isValue, Fin.one_eq_zero_iff]
  rfl

lemma sampled_repeatPlan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s n call : ℕ) (anchor center x : E) :
    QueryPlan.sampledEval (channelReply P g) ξ
      (repeatPlan (stepPlan t s anchor center) n x) call =
      ContinuizedSimilarQuasar.iterateSamples
        (batchStep P (batchSize t s) t.L1 (localScale t s) (radius t s)
          (regularization t s) anchor center g) n x
        (fun j : Fin n =>
          ((fun i : Fin (batchSize t s) => ξ (call + ((1 + batchSize t s + 1) + batchSize t s) * j.val + i.val)),
           (fun i : Fin (batchSize t s) => ξ (call + ((1 + batchSize t s + 1) + batchSize t s) * j.val + batchSize t s + 1 + i.val)))) := by
  induction n generalizing x call with
  | zero => rfl
  | succ n ih =>
    rw [repeatPlan, QueryPlan.sampledEval_bind, ih]
    simp only [ContinuizedSimilarQuasar.iterateSamples, Fin.val_zero, mul_zero, add_zero,
      Fin.val_succ, sampled_stepPlan]
    congr 1
    funext j
    apply Prod.ext <;> funext i <;> simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]

lemma sampled_stagePlan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval (channelReply P g) ξ (stagePlan t s anchor center) call =
      confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t) t.L1
        (localScale t s) (radius t s) (regularization t s) anchor center g
        (fun j : Fin (repetitions t) => fun k : Fin (innerSteps t s) =>
          ((fun i : Fin (batchSize t s) =>
            ξ (call + (((1 + batchSize t s + 1) + batchSize t s) * innerSteps t s) * j.val +
              ((1 + batchSize t s + 1) + batchSize t s) * k.val + i.val)),
           (fun i : Fin (batchSize t s) =>
            ξ (call + (((1 + batchSize t s + 1) + batchSize t s) * innerSteps t s) * j.val +
              ((1 + batchSize t s + 1) + batchSize t s) * k.val + batchSize t s + 1 + i.val)))) := by
  erw [stagePlan, QueryPlan.sampledEval_map, QueryPlan.sampledEval_traverse]
  unfold confidenceOutput
  apply congrArg (aggregate (radius t s) center)
  funext i
  rw [List.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some]
  exact sampled_repeatPlan P g ξ t s (innerSteps t s) _ anchor center center

lemma sampled_finalPlan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (call : ℕ) (anchor x : E) :
    QueryPlan.sampledEval (channelReply P g) ξ (finalPlan t anchor x) call =
      residualOutput P t anchor x
        (RobustGradient.pilotCenter (t.ε / 16) (fun j : Fin (repetitions t) =>
          (1 / (finalBatchSize t : ℝ)) • ∑ i : Fin (finalBatchSize t),
            g x (ξ (call + finalBatchSize t * j.val + i.val)))) := by
  rw [finalPlan, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_traverse]
  simp [QueryPlan.sampledEval, channelReply, residualOutput, sampled_meanPlan]

lemma sampled_stage_block (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval (channelReply P g) ξ (stagePlan t s anchor center) call =
      blockOutput P t s anchor center g (fun i => ξ (call + i.val)) := by
  rw [sampled_stagePlan]
  unfold blockOutput
  apply congrArg (confidenceOutput P (innerSteps t s) (batchSize t s) (repetitions t)
    t.L1 (localScale t s) (radius t s) (regularization t s) anchor center g)
  funext j k
  apply Prod.ext <;> funext i <;>
    simp [stageSamples, trialSamples, stepSamples, ClippedExtragradient.splitBatches,
      ClippedExtragradient.groupSamples, sampleIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma sampled_final_block (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (call : ℕ) (anchor x : E) :
    QueryPlan.sampledEval (channelReply P g) ξ (finalPlan t anchor x) call =
      finalBlock P t anchor x g (fun i => ξ (call + i.val)) := by
  rw [sampled_finalPlan]
  simp only [finalBlock, finalEstimate, finalSamples, Nat.add_assoc]

lemma sampled_run_trace (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s n call : ℕ) (anchor center : E) (hindex : s + n = stageCount t) :
    QueryPlan.sampledEval (channelReply P g) ξ (runPlan t s n anchor center) call =
      (StochasticGeneralized.blockTrace (phaseCost t) (phaseNext P t g) (s, anchor, center)
        (fun j => ξ (call + j)) (n + 1)).1.2.2 := by
  induction n generalizing s call anchor center with
  | zero =>
    have hs : s = stageCount t := by omega
    erw [runPlan, sampled_final_block, StochasticGeneralized.blockTrace_start_succ,
      StochasticGeneralized.blockTrace_zero]
    simp only [phaseNext, phaseReply, phaseCost, hs, lt_self_iff_false, ite_false]
    rfl
  | succ n ih =>
    have hs : s < stageCount t := by omega
    conv_rhs => rw [StochasticGeneralized.blockTrace_start_succ]
    erw [runPlan, QueryPlan.sampledEval_bind, sampled_stage_block, ih (s + 1) _ _ _ (by omega)]
    simp only [phaseNext, phaseReply, phaseCost, hs, ite_true, Nat.add_assoc]
    by_cases hn : n = 0
    · have hnext : ¬s + 1 < stageCount t := by omega
      simp only [hn, ite_true, hnext, ite_false]
      rfl
    · have hnext : s + 1 < stageCount t := by omega
      simp only [hn, ite_false, hnext, ite_true]
      rfl

lemma execute_trace [MeasurableSpace Ω] (law : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (P : E → E) (g : E → Ω → E) (t : Tuning) (x0 : E) (K : ℕ)
    (hK : runCalls t 0 (stageCount t) ≤ K) (seed : Unit) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ q ω => channelReply P g q ω }
      (algorithm t x0) (fun _ => K) seed ξ =
      (StochasticGeneralized.blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0)
        ξ (stageCount t + 1)).1.2.2 := by
  have hh := QueryPlan.execute_sampledChannels_of_le (channelReply P g) (0, x0) x0
    (runPlan t 0 (stageCount t) x0 x0)
    { Seed := fun _ => Ω, law := law, answer := fun _ q ω => channelReply P g q ω }
    (fun _ => rfl) (fun _ => K) (fun _ => hK) (fun _ _ _ => rfl) seed ξ
  change execute { Seed := fun _ => Ω, law := law, answer := fun _ q ω => channelReply P g q ω }
    (algorithm t x0) (fun _ => K) seed ξ = _ at hh
  rw [hh]
  simp only [cast_eq]
  rw [sampled_run_trace P g ξ t 0 (stageCount t) 0 x0 x0 (by omega)]
  simp only [Nat.zero_add]

end OracleTemplate.ProjectedClippedExtragradient
