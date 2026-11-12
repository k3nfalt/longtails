import LongTails.Proofs.StochasticMfcqSampling

namespace LongTails.Proofs.StochasticMfcqQuerySafety
open OracleTemplate
open LongTails.Algorithms.StochasticEnvelopeProgram
open RecursiveEnvelopeExecution

variable {Q R U V : Type*}

def safeAt (safe : Q → Prop) (reply : ℕ → Q → R) :
    {n : ℕ} → QueryPlan Q R U n → ℕ → Prop
  | _, .done _, _ => True
  | _, .ask q next, call => safe q ∧ safeAt safe reply (next (reply call q)) (call + 1)

lemma safeAt_bind (safe : Q → Prop) (reply : ℕ → Q → R) {n m : ℕ}
    (plan : QueryPlan Q R U n) (next : U → QueryPlan Q R V m) (call : ℕ) :
    safeAt safe reply (plan.bind next) call ↔ safeAt safe reply plan call ∧
      safeAt safe reply (next (evalAt reply plan call)) (call + n) := by
  induction plan generalizing call with
  | done value => simp [QueryPlan.bind, safeAt, evalAt]
  | @ask n q rest ih =>
    simp only [QueryPlan.bind, safeAt, evalAt, ih]
    have he : call + 1 + n = call + (n + 1) := by omega
    rw [he]
    tauto

lemma safeAt_map (safe : Q → Prop) (reply : ℕ → Q → R) {n : ℕ}
    (plan : QueryPlan Q R U n) (f : U → V) (call : ℕ) :
    safeAt safe reply (plan.map f) call ↔ safeAt safe reply plan call := by
  induction plan generalizing call with
  | done value => rfl
  | ask q next ih => exact and_congr_right (fun _ => ih (reply call q) (call + 1))

lemma safeAt_cast (safe : Q → Prop) (reply : ℕ → Q → R) {n m : ℕ}
    (h : n = m) (plan : QueryPlan Q R U n) (call : ℕ) :
    safeAt safe reply (castPlan h plan) call ↔ safeAt safe reply plan call := by
  subst m
  rfl

lemma safeAt_collect (safe : Q → Prop) (reply : ℕ → Q → R) {b : ℕ}
    (n : ℕ) (plans : Fin n → QueryPlan Q R U b)
    (h : ∀ i call, safeAt safe reply (plans i) call) (call : ℕ) :
    safeAt safe reply (collectPlans n plans) call := by
  induction n generalizing call with
  | zero => trivial
  | succ n ih =>
    rw [collectPlans, safeAt_bind]
    refine ⟨h 0 call, ?_⟩
    rw [safeAt_map]
    exact ih (fun i => plans i.succ) (fun i call => h i.succ call) _

lemma safe_query_advance (safe : Q → Prop) (reply : ℕ → Q → R) (q0 : Q)
    (h0 : safe q0) {n : ℕ} (plan : QueryPlan Q R U n) (call elapsed : ℕ)
    (hp : safeAt safe reply plan call) :
    safe (QueryPlan.query q0 (StochasticGradient.advance
      (fun j s => QueryPlan.update s (reply j (QueryPlan.query q0 s))) elapsed call ⟨n, plan⟩)) := by
  induction elapsed generalizing n call with
  | zero =>
    cases plan with
    | done value => exact h0
    | ask q next => exact hp.1
  | succ elapsed ih =>
    cases plan with
    | done value => exact ih (.done value) (call + 1) trivial
    | ask q next => exact ih (next (reply call q)) (call + 1) hp.2

lemma indexedState_advance (O : Oracle Q R) (A : Algorithm Q R U)
    (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    (executeIndexedState O A seed ξ n).1 =
      StochasticGradient.advance
        (fun k state => A.update state (executeAnswerAt O A seed ξ k (A.query state)))
        n 0 (A.initial seed) := by
  rw [executeIndexedState_eq_executeAnswerAt]
  generalize A.initial seed = state
  generalize (0 : ℕ) = call
  induction n generalizing state call with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ _

lemma trace_safe_of_queries (safe : Q → Prop) (O : Oracle Q R) (A : Algorithm Q R U)
    (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (h : ∀ n, safe (A.query (executeIndexedState O A seed ξ n).1).2) (K : ℕ) :
    ∀ item ∈ (executeWithTrace O A (fun _ => K) seed ξ).2, safe item.1.2 := by
  rw [executeWithTrace_eq_executeIndexedState]
  change ∀ item ∈ (executeIndexedState O A seed ξ K).2, safe item.1.2
  induction K with
  | zero => simp [executeIndexedState]
  | succ K ih =>
    intro item hi
    simp only [executeIndexedState, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact ih item hi
    · exact h K

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq

def feasibleQuery (p : Params) (I : Problem p) (q : p.E × p.E) : Prop :=
  feasible p I q.1 ∧ feasible p I q.2

lemma safeAt_batchPlan (p : Params) (I : Problem p)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (k call : ℕ) (s : State p) (i : Fin (replicas p))
    (hs : feasibleQuery p I (s.1, s.2.1)) :
    safeAt (feasibleQuery p I) reply (batchPlan p k s i) call := by
  rw [batchPlan, safeAt_cast, safeAt_map]
  apply safeAt_collect
  intro j call
  exact ⟨hs, trivial⟩

lemma safeAt_stepPlan (p : Params) (I : Problem p)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (k call : ℕ) (s : State p) (hs : feasibleQuery p I (s.1, s.2.1)) :
    safeAt (feasibleQuery p I) reply (stepPlan p k s) call := by
  rw [stepPlan, safeAt_map]
  apply safeAt_collect
  intro i call
  exact safeAt_batchPlan p I reply k call s i hs

lemma safeAt_remaining (p : Params) (I : Problem p)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (hs : ∀ k < outerSteps p, feasibleQuery p I
      ((StochasticMfcqExecution.stateAt p reply k).1,
        (StochasticMfcqExecution.stateAt p reply k).2.1))
    (n k : ℕ) (hn : k + n ≤ outerSteps p) :
    safeAt (feasibleQuery p I) reply
      (slotPlan (fun j => batchSize p j * replicas p) (stepPlan p) n k
        (StochasticMfcqExecution.stateAt p reply k))
      (slotCalls (fun j => batchSize p j * replicas p) k 0) := by
  induction n generalizing k with
  | zero => trivial
  | succ n ih =>
    simp only [slotPlan, slotCalls, safeAt_bind]
    refine ⟨safeAt_stepPlan p I reply k _ _ (hs k (by omega)), ?_⟩
    rw [← StochasticMfcqExecution.stateAt, ← StochasticEnvelopeExecution.slotCalls_prefix_succ]
    exact ih (k + 1) (by omega)

lemma safeAt_program (p : Params) (I : Problem p)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (hs : ∀ k < outerSteps p, feasibleQuery p I
      ((StochasticMfcqExecution.stateAt p reply k).1,
        (StochasticMfcqExecution.stateAt p reply k).2.1)) :
    safeAt (feasibleQuery p I) reply (program p) 0 := by
  unfold program calls
  rw [safeAt_map]
  exact safeAt_remaining p I reply hs (outerSteps p) 0 (by omega)

lemma execute_trace_safe (p : Params) (I : Problem p) (R : Regularity p I)
    (O : Oracle (p.E × p.E) (Primitive p × Primitive p))
    (seed : Unit) (ξ : (k : ℕ) → O.Seed k)
    (reply : ℕ → p.E × p.E → Primitive p × Primitive p)
    (hr : ∀ history query, O.answer history query (ξ history.length) = reply history.length query.2)
    (hs : ∀ k < outerSteps p, feasibleQuery p I
      ((StochasticMfcqExecution.stateAt p reply k).1,
        (StochasticMfcqExecution.stateAt p reply k).2.1)) (K : ℕ) :
    ∀ item ∈ (executeWithTrace O (LongTails.Algorithms.StochasticMfcq.algorithm p)
      (fun _ => K) seed ξ).2, feasibleQuery p I item.1.2 := by
  apply trace_safe_of_queries
  intro n
  erw [indexedState_advance O (LongTails.Algorithms.StochasticMfcq.algorithm p) seed ξ n]
  have he : ∀ k query, executeAnswerAt O (LongTails.Algorithms.StochasticMfcq.algorithm p)
      seed ξ k query = reply k query.2 := by
    intro k query
    unfold executeAnswerAt
    rw [hr]
    erw [executeIndexedState_length]
  simp only [he]
  exact safe_query_advance (feasibleQuery p I) reply (p.x0, p.x0)
    ⟨R.initialFeasible, R.initialFeasible⟩ (program p) 0 n (safeAt_program p I reply hs)

end LongTails.Proofs.StochasticMfcqQuerySafety
