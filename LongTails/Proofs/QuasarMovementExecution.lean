import LongTails.Algorithms.MovementQuasar
import LongTails.Proofs.ContinuizedQuasarExecution
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

lemma eval_innerPlan (p : Params) (g : Fin p.n × p.E → p.E) (w : p.E)
    (k : ℕ) (s : p.E × p.E) (samples : Fin k → ℝ × Fin p.n) :
    QueryPlan.eval g (innerPlan p (fun i => g (i, w)) k s samples) =
      innerRun p g w k s samples := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [innerPlan, QueryPlan.eval_bind, stepPlan, QueryPlan.eval, ih]
      rfl

lemma eval_epochPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (s : p.E × p.E) (samples : Fin p.n → ℝ × Fin p.n) :
    QueryPlan.eval g (epochPlan p s samples) = epochRun p g s samples := by
  simp only [epochPlan, QueryPlan.eval_bind, eval_cachePlan]
  exact eval_innerPlan p g s.1 _ s samples

lemma eval_allPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (S : ℕ) (s : p.E × p.E)
    (samples : Fin S → Fin p.n → ℝ × Fin p.n) :
    QueryPlan.eval g (allPlan p S s samples) = run p g S s samples := by
  induction S generalizing s with
  | zero => rfl
  | succ S ih =>
      simp only [allPlan, QueryPlan.eval_bind, eval_epochPlan, ih]
      rfl

lemma execute_accelerated (p : Params) (g : Fin p.n × p.E → p.E)
    (seed : (accelerated p).Seed) (K : ℕ) (hK : (p.n + p.n) * epochs p ≤ K) :
    execute {answer := fun _ (_, q) _ => g q} (accelerated p) (fun _ => K) seed =
      (run p g (epochs p) (p.x0, p.x0) seed).1 := by
  change execute {answer := fun _ (_, q) _ => g q} (QueryPlan.algorithm _ _ _ _ _) (fun _ => _) _ = _
  erw [QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ hK, QueryPlan.eval_map, eval_allPlan]

end OracleTemplate.ContinuizedSimilarQuasar.Movement
