import LongTails.Algorithms.RecursiveEnvelope
import LongTails.Proofs.ExecutionHistory

namespace LongTails.Proofs.RecursiveEnvelopeExecution

open OracleTemplate

variable {Q R U V : Type*}

def evalAt (reply : ℕ → Q → R) : {k : ℕ} → QueryPlan Q R U k → ℕ → U
  | _, .done value, _ => value
  | _, .ask q next, call => evalAt reply (next (reply call q)) (call + 1)

lemma evalAt_bind (reply : ℕ → Q → R) {k m : ℕ} (plan : QueryPlan Q R U k)
    (next : U → QueryPlan Q R V m) (call : ℕ) :
    evalAt reply (plan.bind next) call = evalAt reply (next (evalAt reply plan call)) (call + k) := by
  induction plan generalizing call with
  | done value => simp [QueryPlan.bind, evalAt]
  | @ask k q rest ih =>
      simp only [QueryPlan.bind, evalAt]
      rw [ih]
      congr 1; omega

lemma evalAt_map (reply : ℕ → Q → R) (f : U → V) {k : ℕ} (plan : QueryPlan Q R U k)
    (call : ℕ) : evalAt reply (plan.map f) call = f (evalAt reply plan call) := by
  induction plan generalizing call with
  | done value => rfl
  | ask q rest ih => exact ih (reply call q) (call + 1)

lemma advance_plan_indexed (reply : ℕ → Q → R) (q0 : Q) {k K : ℕ}
    (plan : QueryPlan Q R U k) (h : k ≤ K) (call : ℕ) :
    StochasticGradient.advance (fun n s => QueryPlan.update s (reply n (QueryPlan.query q0 s)))
      K call ⟨k, plan⟩ = ⟨0, .done (evalAt reply plan call)⟩ := by
  induction plan generalizing K call with
  | done value =>
      induction K generalizing call with
      | zero => rfl
      | succ K ih => exact ih (Nat.zero_le K) (call + 1)
  | @ask k q rest ih =>
      cases K with
      | zero => omega
      | succ K => exact ih (reply call q) (by omega) (call + 1)

lemma execute_plan_indexed {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    {k K : ℕ} (plan : S → QueryPlan Q R U k) (oracle : Oracle Q R)
    (seed : S) (ξ : (n : ℕ) → oracle.Seed n) (h : k ≤ K) :
    execute oracle (QueryPlan.algorithm law q0 u0 k plan) (fun _ => K) seed ξ =
      evalAt (fun n q => executeAnswerAt oracle (QueryPlan.algorithm law q0 u0 k plan)
        seed ξ n (0, q)) (plan seed) 0 := by
  erw [execute_advance_history]
  change QueryPlan.output u0 (StochasticGradient.advance
    (fun n s => QueryPlan.update s (executeAnswerAt oracle
      (QueryPlan.algorithm law q0 u0 k plan) seed ξ n (0, QueryPlan.query q0 s)))
      K 0 ⟨k, plan seed⟩) = _
  exact congrArg (QueryPlan.output u0) (advance_plan_indexed
    (fun n q => executeAnswerAt oracle (QueryPlan.algorithm law q0 u0 k plan)
      seed ξ n (0, q)) q0 (plan seed) h 0)

open LongTails.Algorithms.RecursiveEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma evalAt_innerPlan {c : ℕ} (reply : ℕ → E → E) (oraclePlan : E → QueryPlan E E E c)
    (L μ α : ℝ) (center : E) (N offset call : ℕ) (state : E × E) :
    evalAt reply (innerPlan oraclePlan L μ α center N state) (offset + c * call) =
      (StochasticGradient.advance
        (fun k s => InexactGradient.step L μ (InexactGradient.momentum L μ α) s
          (evalAt reply (oraclePlan (InexactGradient.query (InexactGradient.momentum L μ α) s))
            (offset + c * k) + μ • (InexactGradient.query (InexactGradient.momentum L μ α) s - center)))
        N call state).1 := by
  induction N generalizing call state with
  | zero => rfl
  | succ N ih =>
      simp only [innerPlan, evalAt_bind, StochasticGradient.advance]
      have he : offset + c * call + c = offset + c * (call + 1) := by ring
      rw [he]
      exact ih (call + 1) _

lemma evalAt_gradientPlan (reply : ℕ → E → E) (L : ℝ) (d m i : ℕ) (x : E) (call : ℕ) :
    evalAt reply (gradientPlan L d m (i + 1) x) call =
      levelSmoothness L d (i + 1) • (x - evalAt reply (proxPlan L d m i x) call) := by
  exact evalAt_map reply _ _ call

lemma evalAt_recoveryPlan (reply : ℕ → E → E) (L : ℝ) (d m i : ℕ) (x : E) (call : ℕ) :
    evalAt reply (recoveryPlan L d m (i + 1) x) call =
      evalAt reply (recoveryPlan L d m i (evalAt reply (proxPlan L d m i x) call))
        (call + m ^ (i + 1)) := by
  exact evalAt_bind reply _ _ call

end LongTails.Proofs.RecursiveEnvelopeExecution
