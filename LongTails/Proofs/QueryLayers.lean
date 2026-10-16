import LongTails.Algorithms.QueryLayers
import LongTails.Proofs.SampledQueryPlan

namespace LongTails.Proofs.QueryLayers

open OracleTemplate LongTails.Algorithms.QueryLayers

variable {Q R U V : Type}

lemma fixed_queries_length [Nonempty R] {k : ℕ} {plan : QueryPlan Q R U k} {qs : List Q}
    (h : FixedQueries plan qs) : qs.length = k := by
  induction h with
  | done value => rfl
  | ask q next qs tail ih =>
    simp only [List.length_cons, ih (Classical.choice inferInstance)]

lemma fixed_queries_trace {k : ℕ} {plan : QueryPlan Q R U k} {qs : List Q}
    (h : FixedQueries plan qs) (reply : ℕ → Q → R) (call : ℕ) :
    queryTrace reply plan call = qs := by
  induction h generalizing call with
  | done value => rfl
  | ask q next qs tail ih =>
    dsimp only [queryTrace]
    rw [ih]

lemma fixed_queries_map {k : ℕ} {plan : QueryPlan Q R U k} {qs : List Q}
    (h : FixedQueries plan qs) (f : U → V) : FixedQueries (plan.map f) qs := by
  induction h with
  | done value => exact .done _
  | ask q next qs tail ih => exact .ask q _ qs ih

lemma fixed_queries_bind {k m : ℕ} {plan : QueryPlan Q R U k} {qs rs : List Q}
    (h : FixedQueries plan qs) (next : U → QueryPlan Q R V m)
    (hn : ∀ value, FixedQueries (next value) rs) : FixedQueries (plan.bind next) (qs ++ rs) := by
  induction h with
  | done value => exact hn value
  | ask q rest qs tail ih => exact .ask q _ (qs ++ rs) ih

lemma padding_plan_fixed (q0 : Q) (value : U) (n : ℕ) :
    FixedQueries (paddingPlan (R := R) q0 value n) (List.replicate n q0) := by
  induction n with
  | zero => exact .done _
  | succ n ih => exact .ask q0 _ _ (fun _ => ih)

lemma query_trace_bind (reply : ℕ → Q → R) {k m : ℕ}
    (plan : QueryPlan Q R U k) (next : U → QueryPlan Q R V m) (call : ℕ) :
    queryTrace reply (plan.bind next) call = queryTrace reply plan call ++
      queryTrace reply (next (QueryPlan.sampledEval (fun q i => reply i q) id plan call)) (call + k) := by
  induction plan generalizing call with
  | done value => simp [QueryPlan.bind, queryTrace, QueryPlan.sampledEval]
  | @ask k q rest ih =>
    simp only [QueryPlan.bind, queryTrace, QueryPlan.sampledEval, id_eq, ih, List.cons_append]
    simp only [Nat.add_comm, Nat.add_left_comm]

lemma fixed_queries_traverse {c : ℕ} (n : ℕ) (plans : Fin n → QueryPlan Q R U c)
    (qs : Fin n → List Q) (h : ∀ i, FixedQueries (plans i) (qs i)) :
    FixedQueries (QueryPlan.traverse n plans) (List.ofFn qs).flatten := by
  induction n with
  | zero => exact .done _
  | succ n ih =>
    simp only [QueryPlan.traverse, List.ofFn_succ, List.flatten_cons]
    apply fixed_queries_bind (h 0)
    intro value
    exact fixed_queries_map (ih (fun i => plans i.succ) (fun i => qs i.succ) (fun i => h i.succ)) _

lemma execution_trace_ofFn (q0 : Q) (reply : ℕ → Q → R) (K call : ℕ)
    (state : Σ k, QueryPlan Q R U k) :
    executionTrace q0 reply K call state =
      List.ofFn (fun i : Fin K => QueryPlan.query q0
        (OracleTemplate.StochasticGradient.advance
          (fun j s => QueryPlan.update s (reply j (QueryPlan.query q0 s))) i call state)) := by
  induction K generalizing call state with
  | zero => rfl
  | succ K ih =>
    simp only [executionTrace, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
      OracleTemplate.StochasticGradient.advance]
    rw [ih]

lemma execution_trace_padded (q0 : Q) (reply : ℕ → Q → R) {k : ℕ}
    (plan : QueryPlan Q R U k) (padding call : ℕ) :
    executionTrace q0 reply (padding + k) call ⟨k, plan⟩ =
      queryTrace reply (paddedPlan q0 plan padding) call := by
  induction plan generalizing call with
  | done value =>
    simp only [Nat.add_zero, paddedPlan, QueryPlan.bind]
    induction padding generalizing call with
    | zero => rfl
    | succ padding ih =>
      simp only [executionTrace, QueryPlan.query, QueryPlan.update, paddingPlan, queryTrace]
      rw [ih]
  | @ask k q rest ih =>
    simp only [Nat.add_succ, executionTrace, QueryPlan.query, QueryPlan.update,
      paddedPlan, QueryPlan.bind, queryTrace]
    exact congrArg (q :: ·) (ih (reply call q) (call + 1))

lemma ask_heq {k l : ℕ} (hkl : k = l) (q : Q)
    (first : R → QueryPlan Q R U k) (second : R → QueryPlan Q R U l)
    (h : ∀ r, HEq (first r) (second r)) : HEq (QueryPlan.ask q first) (QueryPlan.ask q second) := by
  cases hkl
  exact heq_of_eq (congrArg (QueryPlan.ask q) (funext (fun r => eq_of_heq (h r))))

lemma bind_assoc_heq {W : Type} {k m n : ℕ} (plan : QueryPlan Q R U k)
    (next : U → QueryPlan Q R V m) (last : V → QueryPlan Q R W n) :
    HEq ((plan.bind next).bind last) (plan.bind (fun value => (next value).bind last)) := by
  induction plan with
  | done value => rfl
  | @ask k q rest ih =>
    exact ask_heq (Nat.add_assoc n m k).symm q _ _ ih

lemma layers_of_heq {k l n : ℕ} {first : QueryPlan Q R U k} {second : QueryPlan Q R U l}
    (hkl : k = l) (he : HEq first second) (hs : Layers second n) : Layers first n := by
  cases hkl
  rw [eq_of_heq he]
  exact hs

end LongTails.Proofs.QueryLayers
