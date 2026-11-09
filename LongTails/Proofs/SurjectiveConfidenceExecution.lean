import LongTails.Algorithms.SurjectiveConfidence
import LongTails.Proofs.SurjectiveProxLinearExecution
import LongTails.Proofs.SampledQueryPlan

set_option backward.isDefEq.respectTransparency false

namespace LongTails.Proofs.SurjectiveConfidenceExecution

open OracleTemplate
open LongTails.Algorithms.SurjectiveConfidence
open LongTails.Setups.StochasticSurjectiveInequalities (Primitive)
open LongTails.Setups.ConfidentStochasticSurjectiveInequalities
open LongTails.Proofs.SurjectiveProxLinearExecution
open LongTails.Proofs.SurjectiveProxLinearTrajectory

lemma sampledEval_shift {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    {k : ℕ} (plan : QueryPlan Q R U k) (a b : ℕ) :
    QueryPlan.sampledEval g (fun j => ξ (a + j)) plan b =
      QueryPlan.sampledEval g ξ plan (a + b) := by
  induction plan generalizing b with
  | done u => rfl
  | ask q next ih =>
      simp only [QueryPlan.sampledEval]
      rw [ih]
      simp only [Nat.add_assoc]

lemma sampledEval_congr {Q R U Ω : Type*} (g : Q → Ω → R)
    {k : ℕ} (plan : QueryPlan Q R U k) (ξ η : ℕ → Ω) (call : ℕ)
    (h : ∀ j, call ≤ j → j < call + k → ξ j = η j) :
    QueryPlan.sampledEval g ξ plan call = QueryPlan.sampledEval g η plan call := by
  induction plan generalizing call with
  | done u => rfl
  | @ask k q next ih =>
      simp only [QueryPlan.sampledEval]
      rw [h call le_rfl (by omega)]
      apply ih
      intro j hj hjk
      apply h j <;> omega

lemma trainingPlan_eval (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (ξ : ℕ → p.problem.Ω) (n : ℕ) (s : LongTails.Algorithms.SurjectiveProxLinear.State p.problem)
    (call : ℕ) :
    QueryPlan.sampledEval (fun q ω => (Z q.1 ω, Z q.2 ω)) ξ (trainingPlan p n s) call =
      ((indexedStep p.problem Z ξ)^[n] (s, call)).1.x := by
  induction n generalizing s call with
  | zero => rfl
  | succ n ih =>
      simp only [trainingPlan, QueryPlan.sampledEval, Function.iterate_succ_apply]
      exact ih _ _

lemma trainingPlan_point (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (ξ : ℕ → p.problem.Ω) (t : Fin (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem + 1)) :
    QueryPlan.sampledEval (fun q ω => (Z q.1 ω, Z q.2 ω)) ξ
      (trainingPlan p (trainingCalls p) ⟨t.val, 0, p.problem.x0, 0, 0⟩) 0 =
        (trajectory p.problem (liftedOracle p.problem Z) ξ t.val).1 := by
  rw [trainingPlan_eval]
  change (rawRun p.problem Z ξ t.val (trainingCalls p)).1.x = _
  have ht := t.isLt
  have h : trainingCalls p = LongTails.Algorithms.SurjectiveProxLinear.initialBatch p.problem +
      t.val + LongTails.Algorithms.SurjectiveProxLinear.certificateBatch p.problem +
      (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem - t.val) := by
    unfold trainingCalls
    omega
  rw [h, run_frozen]

noncomputable def candidate (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (t : Fin (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem + 1))
    (ξ : ℕ → p.problem.Ω) : p.problem.E × Primitive p.problem :=
  let x := (trajectory p.problem (liftedOracle p.problem Z) ξ t.val).1
  (x, robustEstimate p (List.ofFn (fun i : Fin (groups p) =>
    List.ofFn (fun j : Fin (batch p) => Z x (ξ (trainingCalls p + batch p * i.val + j.val))))))

lemma samplePlan_eval (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (ξ : ℕ → p.problem.Ω) (x : p.problem.E) (n call : ℕ) :
    QueryPlan.sampledEval (fun q ω => (Z q.1 ω, Z q.2 ω)) ξ (samplePlan p x n) call =
      List.ofFn (fun i : Fin n => Z x (ξ (call + i.val))) := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih =>
      simp only [samplePlan, QueryPlan.sampledEval, QueryPlan.sampledEval_map, ih,
        List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
      simp only [Nat.add_left_comm, Nat.add_comm]

lemma trialPlan_eval (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (ξ : ℕ → p.problem.Ω) (t : Fin (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem + 1)) :
    QueryPlan.sampledEval (fun q ω => (Z q.1 ω, Z q.2 ω)) ξ (trialPlan p t) 0 =
      candidate p Z t ξ := by
  simp only [trialPlan, QueryPlan.sampledEval_bind, trainingPlan_point, Nat.zero_add,
    QueryPlan.sampledEval_map, certificatePlan, QueryPlan.sampledEval_traverse,
    samplePlan_eval, candidate]

lemma candidate_congr (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (t : Fin (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem + 1))
    (ξ η : ℕ → p.problem.Ω) (h : ∀ j < trialCalls p, ξ j = η j) :
    candidate p Z t ξ = candidate p Z t η := by
  rw [← trialPlan_eval, ← trialPlan_eval]
  apply sampledEval_congr
  intro j _ hj
  exact h j (by simpa using hj)

lemma plan_eval (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (ξ : ℕ → p.problem.Ω)
    (t : Fin (replicas p) → Fin (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem + 1)) :
    QueryPlan.sampledEval (fun q ω => (Z q.1 ω, Z q.2 ω)) ξ (plan p t) 0 =
      select p (List.ofFn (fun i : Fin (replicas p) =>
        candidate p Z (t i) (fun j => ξ (trialCalls p * i.val + j)))) := by
  rw [plan, QueryPlan.sampledEval_map, QueryPlan.sampledEval_traverse]
  congr 2
  funext i
  rw [Nat.zero_add]
  have h := sampledEval_shift (fun q ω => (Z q.1 ω, Z q.2 ω)) ξ
    (trialPlan p (t i)) (trialCalls p * i.val) 0
  simp only [Nat.add_zero] at h
  rw [← h, trialPlan_eval]

lemma execution_output (p : Params) (Z : p.problem.E → p.problem.Ω → Primitive p.problem)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → p.problem.Ω)) (K : ℕ)
    (t : Fin (replicas p) → Fin (LongTails.Algorithms.SurjectiveProxLinear.iterations p.problem + 1))
    (ξ : ℕ → p.problem.Ω) (hK : trialCalls p * replicas p ≤ K) :
    execute { Seed := fun _ => p.problem.Ω
              law := P
              answer := fun _ (_, q) ω => (Z q.1 ω, Z q.2 ω) }
      (algorithm p) (fun _ => K) t ξ =
      select p (List.ofFn (fun i : Fin (replicas p) =>
        candidate p Z (t i) (fun j => ξ (trialCalls p * i.val + j)))) := by
  exact (QueryPlan.execute_sampledPlan_of_le (seedLaw p) P
    (p.problem.x0, p.problem.x0) (p.problem.x0, 0) (trialCalls p * replicas p) K
    (plan p) (fun q ω => (Z q.1 ω, Z q.2 ω)) t ξ hK).trans (plan_eval p Z ξ t)

end LongTails.Proofs.SurjectiveConfidenceExecution
