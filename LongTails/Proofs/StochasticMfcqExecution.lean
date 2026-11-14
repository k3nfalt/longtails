import LongTails.Algorithms.StochasticMfcq
import LongTails.Proofs.StochasticEnvelopeExecution

namespace LongTails.Proofs.StochasticMfcqExecution

open OracleTemplate
open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq
open LongTails.Algorithms.StochasticEnvelopeProgram
open RecursiveEnvelopeExecution StochasticEnvelopeExecution

lemma eval_batchPlan (p : Params)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (k call : ℕ) (s : State p) (i : Fin (replicas p)) :
    evalAt reply (batchPlan p k s i) call =
      (batchSize p k : ℝ)⁻¹ • ∑ j : Fin (batchSize p k),
        sampleValue p k (reply (call + j.val) (s.1, s.2.1)) +
      if k % epochLength p = 0 then 0 else s.2.2.1 i := by
  simp only [batchPlan, evalAt_castPlan, evalAt_map, evalAt_collectPlans, evalAt,
    Nat.zero_add, Nat.one_mul]

lemma eval_stepPlan (p : Params)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (k call : ℕ) (s : State p) :
    evalAt reply (stepPlan p k s) call = nextState p s (fun i =>
      (batchSize p k : ℝ)⁻¹ • ∑ j : Fin (batchSize p k),
        sampleValue p k (reply (call + batchSize p k * i.val + j.val) (s.1, s.2.1)) +
      if k % epochLength p = 0 then 0 else s.2.2.1 i) := by
  simp only [stepPlan, evalAt_map, evalAt_collectPlans, eval_batchPlan]

noncomputable def stateAt (p : Params)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p) : ℕ → State p
  | 0 => initial p
  | k + 1 => evalAt reply (stepPlan p k (stateAt p reply k))
      (slotCalls (fun j => batchSize p j * replicas p) k 0)

lemma stateAt_succ (p : Params)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p) (k : ℕ) :
    stateAt p reply (k + 1) = nextState p (stateAt p reply k) (fun i =>
      (batchSize p k : ℝ)⁻¹ • ∑ j : Fin (batchSize p k), sampleValue p k
        (reply (slotCalls (fun l => batchSize p l * replicas p) k 0 +
          batchSize p k * i.val + j.val) ((stateAt p reply k).1, (stateAt p reply k).2.1)) +
      if k % epochLength p = 0 then 0 else (stateAt p reply k).2.2.1 i) := by
  rw [stateAt, eval_stepPlan]

lemma eval_remaining (p : Params)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p) (n k : ℕ) :
    evalAt reply (slotPlan (fun j => batchSize p j * replicas p) (stepPlan p)
      n k (stateAt p reply k)) (slotCalls (fun j => batchSize p j * replicas p) k 0) =
      stateAt p reply (k + n) := by
  induction n generalizing k with
  | zero => simp [slotPlan, evalAt]
  | succ n ih =>
    rw [evalAt_slotPlan_succ, ← stateAt, ← slotCalls_prefix_succ, ih]
    congr 1
    omega

lemma eval_program (p : Params)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p) :
    evalAt reply (program p) 0 =
      ((stateAt p reply (outerSteps p)).1, (stateAt p reply (outerSteps p)).2.2.2.2) := by
  unfold program calls
  rw [evalAt_map]
  have he := eval_remaining p reply (outerSteps p) 0
  simpa only [stateAt, slotCalls, Nat.zero_add] using
    congrArg (fun s : State p => (s.1, s.2.2.2.2)) he

lemma execute_stateAt (p : Params) (O : Oracle (p.E × p.E) (Primitive p × Primitive p))
    (K : ℕ) (seed : Unit) (ξ : (k : ℕ) → O.Seed k)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (hr : ∀ history query, O.answer history query (ξ history.length) = reply history.length query.2)
    (hK : calls p ≤ K) :
    execute O (LongTails.Algorithms.StochasticMfcq.algorithm p) (fun _ => K) seed ξ =
      ((stateAt p reply (outerSteps p)).1, (stateAt p reply (outerSteps p)).2.2.2.2) := by
  have he := execute_complete (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ :
      MeasureTheory.ProbabilityMeasure Unit) (p.x0, p.x0) (p.x0, 0)
    (fun _ : Unit => ⟨calls p, program p⟩) O K seed ξ reply hr hK
  exact he.trans (eval_program p reply)

end LongTails.Proofs.StochasticMfcqExecution
