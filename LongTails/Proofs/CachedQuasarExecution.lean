import LongTails.Algorithms.CachedQuasarOracle
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.SimilarQuasar

open LongTails.Setups.SimilarFiniteSumQuasar

lemma head_ofFn {E : Type*} {n : ℕ} [NeZero n] (v : Fin n → E) (fallback : E) :
    (List.ofFn v).headD fallback = v 0 := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => simp [List.ofFn_succ]

lemma eval_fullPlan (p : Params) (g : Fin p.n × p.E → p.E) (w : p.E) :
    QueryPlan.eval g (fullPlan p w) = (FiniteSum.fullGradient g w, g (0, w)) := by
  simp only [fullPlan, QueryPlan.eval_map, QueryPlan.eval_traverse, QueryPlan.eval,
    List.sum_ofFn, FiniteSum.fullGradient, head_ofFn]

lemma eval_innerPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (θ : ℝ) (w : p.E) (k : ℕ) (s : p.E × p.E) :
    QueryPlan.eval g (innerPlan p θ (FiniteSum.fullGradient g w) (g (0, w)) k s) =
      innerRun g p.γ θ p.μ w k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp only [innerPlan, QueryPlan.eval, ih, innerRun, FiniteSum.estimator]

lemma eval_epochPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (θ : ℝ) (m : ℕ) (s : p.E × p.E) :
    QueryPlan.eval g (epochPlan p θ m s) = epoch g p.γ θ p.μ m s := by
  simp only [epochPlan, QueryPlan.eval_bind, eval_fullPlan, eval_innerPlan, epoch]

lemma eval_allPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (θ : ℝ) (m S : ℕ) (s : p.E × p.E) :
    QueryPlan.eval g (allPlan p θ m S s) = run g p.γ θ p.μ m S s := by
  induction S generalizing s with
  | zero => rfl
  | succ S ih => simp only [allPlan, QueryPlan.eval_bind, eval_epochPlan, ih, run]

lemma execute_cachedQuasar (p : Params) (g : Fin p.n × p.E → p.E)
    (θ : ℝ) (m S : ℕ) (seed : Unit) :
    execute { answer := fun _ (_, q) _ => g q } (cachedQuasar p θ m S)
      (fun _ => ((m + 1 * p.n) * S)) seed =
      (run g p.γ θ p.μ m S (p.x0, p.x0)).1 := by
  unfold cachedQuasar
  erw [QueryPlan.execute_plan, QueryPlan.eval_map, eval_allPlan]

end OracleTemplate.SimilarQuasar
