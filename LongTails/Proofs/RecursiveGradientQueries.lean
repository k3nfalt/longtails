import LongTails.Algorithms.RecursiveGradientQueries
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.NonconvexFiniteSum

open LongTails.Setups.FiniteSumSmoothNonconvex

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eval_fullGradientPlan (g : Fin n × E → E) (x : E) :
    QueryPlan.eval g (fullGradientPlan x) = FiniteSum.fullGradient g x := by
  simp [fullGradientPlan, QueryPlan.eval_map, QueryPlan.eval_traverse,
    QueryPlan.eval, List.sum_ofFn, FiniteSum.fullGradient]

lemma eval_differencePlan (g : Fin n × E → E) {b : ℕ}
    (x y : E) (samples : Fin b → Fin n) :
    QueryPlan.eval g (differencePlan x y samples) =
      differenceBatch g b x y (List.ofFn samples) := by
  simp [differencePlan, QueryPlan.eval_map, QueryPlan.eval_traverse,
    QueryPlan.eval, differenceBatch, List.map_ofFn, Function.comp_def]

lemma eval_recursivePlan (g : Fin n × E → E) (η : ℝ) (b k : ℕ)
    (x v : E) (samples : Fin k → Fin b → Fin n) :
    QueryPlan.eval g (recursivePlan η b k x v samples) =
      recursiveRun g η b x v (List.ofFn (fun j => List.ofFn (samples j))) := by
  induction k generalizing x v with
  | zero => rfl
  | succ k ih =>
      simp only [recursivePlan, QueryPlan.eval_bind, QueryPlan.eval_map,
        eval_differencePlan, ih, List.ofFn_succ, recursiveRun]

lemma eval_epochPlan (g : Fin n × E → E) (η : ℝ) (b k : ℕ)
    (x : E) (samples : Fin k → Fin b → Fin n) :
    QueryPlan.eval g (epochPlan η b k x samples) =
      recursiveRun g η b x (FiniteSum.fullGradient g x)
        (List.ofFn (fun j => List.ofFn (samples j))) := by
  simp only [epochPlan, QueryPlan.eval_bind, eval_fullGradientPlan, eval_recursivePlan]

lemma eval_allEpochsPlan (g : Fin n × E → E) (η : ℝ) (b k S : ℕ)
    (x : E) (samples : Fin S → Fin k → Fin b → Fin n) :
    QueryPlan.eval g (allEpochsPlan η b k S x samples) =
      recursiveEpochs g η b x
        (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (samples s j)))) := by
  induction S generalizing x with
  | zero => rfl
  | succ S ih =>
      simp only [allEpochsPlan, QueryPlan.eval_bind, QueryPlan.eval_map,
        eval_epochPlan, ih, List.ofFn_succ, recursiveEpochs]

lemma execute_recursiveGradient [NeZero n] (g : Fin n × E → E) (η : ℝ)
    (b k S : ℕ) [NeZero S] (x0 : E) (seed : RecursiveSeeds n b k S) :
    execute { answer := fun _ (_, q) _ => g q } (recursiveGradient η b k S x0)
        (fun _ => ((2 * b * k + 1 * n) * S)) seed =
      (recursiveEpochs g η b x0
        (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed.1 s j))))).2.getD
          seed.2.val x0 := by
  unfold recursiveGradient
  erw [QueryPlan.execute_plan, QueryPlan.eval_map, eval_allEpochsPlan]

lemma recursiveRun_length (g : Fin n × E → E) (η : ℝ) (b : ℕ)
    (x v : E) (samples : List (List (Fin n))) :
    (recursiveRun g η b x v samples).2.length = samples.length + 1 := by
  induction samples generalizing x v with
  | nil => rfl
  | cons sample tail ih => simp only [recursiveRun, List.length_cons, ih]

lemma recursiveEpochs_length (g : Fin n × E → E) (η : ℝ) (b k S : ℕ)
    (x : E) (samples : Fin S → Fin k → Fin b → Fin n) :
    (recursiveEpochs g η b x
      (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (samples s j))))).2.length =
        (k + 1) * S := by
  induction S generalizing x with
  | zero => simp [recursiveEpochs]
  | succ S ih =>
      simp only [List.ofFn_succ, recursiveEpochs, List.length_append,
        recursiveRun_length, List.length_ofFn, ih, Nat.mul_succ]
      omega

end OracleTemplate.NonconvexFiniteSum
