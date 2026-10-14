import LongTails.Algorithms.RandomReshuffling
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.RandomReshuffling

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

lemma eval_passPlan (g : I → E → E) (η : ℝ) (order : List I) (x : E) :
    QueryPlan.eval (fun q => g q.1 q.2) (passPlan η order x) = pass g η order x := by
  induction order generalizing x with
  | nil => rfl
  | cons i is ih => exact ih (x - η • g i x)

lemma eval_cast {Q R U : Type*} (g : Q → R) {k m : ℕ} (h : k = m)
    (plan : QueryPlan Q R U k) :
    QueryPlan.eval g (h ▸ plan) = QueryPlan.eval g plan := by subst m; rfl

lemma eval_epochPlan {n : ℕ} (g : Fin n → E → E) (η : ℝ)
    (order : Equiv.Perm (Fin n)) (x : E) :
    QueryPlan.eval (fun q => g q.1 q.2) (epochPlan η order x) =
      pass g η (List.ofFn order) x := by
  unfold epochPlan
  rw [eval_cast, eval_passPlan]

lemma eval_epochsPlan {n : ℕ} (g : Fin n → E → E) (η : ℝ) (K : ℕ)
    (x : E) (orders : Fin K → Equiv.Perm (Fin n)) :
    QueryPlan.eval (fun q => g q.1 q.2) (epochsPlan η K x orders) =
      epochs g η (List.ofFn (fun k => List.ofFn (orders k))) x := by
  induction K generalizing x with
  | zero => rfl
  | succ K ih =>
    simp only [epochsPlan, QueryPlan.eval_bind, eval_epochPlan, ih, List.ofFn_succ, epochs]

lemma execute_algorithm {n : ℕ} [NeZero n] (g : Fin n → E → E)
    (η : ℝ) (K : ℕ) (x0 : E) (seed : Seeds n K) :
    execute { answer := fun _ (_, q) _ => g q.1 q.2 } (algorithm η K x0) (fun _ => (n * K)) seed =
      epochs g η (List.ofFn (fun k => List.ofFn (seed k))) x0 := by
  unfold algorithm
  erw [QueryPlan.execute_plan (g := fun q : Fin n × E => g q.1 q.2), eval_epochsPlan]

end OracleTemplate.RandomReshuffling
