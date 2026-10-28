import LongTails.Algorithms.GradientOnlyQuasar
import LongTails.Proofs.QueryPlan
import LongTails.Proofs.Execution

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

lemma eval_plan (q : Params) (g : q.E → q.E) (k : ℕ) (s : ℝ × q.E × q.E)
    (samples : Fin k → ℝ) : QueryPlan.eval g (plan q k s samples) = run q g k s samples := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [plan, QueryPlan.eval, ih]
      rfl

lemma execute_accelerated (q : Params) (g : q.E → q.E) (seed : (accelerated q).Seed) :
    execute {answer := fun _ (_, x) _ => g x} (accelerated q) (fun _ => calls q) seed =
      (run q g (calls q) (0, q.x0, q.x0) seed).2.1 := by
  change execute {answer := fun _ (_, x) _ => g x} (QueryPlan.algorithm _ _ _ _ _) (fun _ => _) _ = _
  erw [QueryPlan.execute_plan, QueryPlan.eval_map, eval_plan]

lemma output_eq_run (q : Params) (O : Oracle q.E q.E) (g : q.E → q.E)
    (ho : ∀ history x seed, O.answer history (0, x) seed = g x)
    (seed : (accelerated q).Seed × ((k : ℕ) → O.Seed k)) :
    output q O seed = (run q g (calls q) (0, q.x0, q.x0) seed.1).2.1 := by
  unfold output
  rw [execute_eq_of_answer_eq O g ho, execute_accelerated]

end OracleTemplate.GradientOnlyQuasar
