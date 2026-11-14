import LongTails.Algorithms.EmpiricalProximalAcceleration
import LongTails.Proofs.KatyushaExecution

namespace LongTails.Proofs.EmpiricalProximalExecution

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex
open LongTails.Algorithms.EmpiricalProximalAcceleration

lemma eval_translatePlan (p : Params) (g : Fin p.n × p.E → p.E)
    (c : p.E) (ι : BatchIndices p) {U : Type*} {K : ℕ}
    (plan : QueryPlan
      (LongTails.Setups.CompositeFiniteSumStronglyConvex.Query (innerParams p c)) p.E U K) :
    QueryPlan.eval g (translatePlan p c ι plan) =
      QueryPlan.eval (Katyusha.answer (innerParams p c)
        (fun q => g (ι q.1, q.2)) (quadraticProx p c)) plan := by
  induction plan with
  | done u => rfl
  | ask q next ih =>
    cases q with
    | gradient i x => exact ih (g (ι i, x))
    | prox a z v => exact ih (quadraticProx p c a z v)

lemma eval_innerPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (c : p.E) (ι : BatchIndices p) (ξ : InnerSeeds p) :
    QueryPlan.eval g (innerPlan p c ι ξ) = innerOutput p g c ι ξ := by
  unfold innerPlan
  erw [eval_translatePlan, QueryPlan.eval_map, Katyusha.eval_allPlan]
  rfl

lemma eval_gradientPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (ι : BatchIndices p) (w : p.E) :
    QueryPlan.eval g (gradientPlan p ι w) = FiniteSum.fullGradient (fun q => g (ι q.1, q.2)) w := by
  simp [gradientPlan, QueryPlan.eval_map, QueryPlan.eval_traverse,
    QueryPlan.eval, List.sum_ofFn, FiniteSum.fullGradient]

lemma eval_stepPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (s : State p) (ξ : BatchIndices p × InnerSeeds p) :
    QueryPlan.eval g (stepPlan p s ξ) = step p g s ξ := by
  unfold stepPlan
  erw [QueryPlan.eval_bind, eval_innerPlan, QueryPlan.eval_map, eval_gradientPlan]
  rfl

lemma eval_outerPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (T : ℕ) (s : State p) (ξ : Seeds p T) :
    QueryPlan.eval g (outerPlan p T s ξ) = run p g T s ξ := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    simp only [outerPlan, QueryPlan.eval_bind, eval_stepPlan, run]
    exact ih _ _

lemma execute_method (p : Params) (g : Fin p.n × p.E → p.E)
    (O : Oracle (Fin p.n × p.E) p.E)
    (hO : ∀ k q seed, O.answer k (0, q) seed = g q)
    (T K : ℕ) (hK : stepCost p * T ≤ K) (ξ : Seeds p T)
    (ω : (k : ℕ) → O.Seed k) :
    execute O (method p T) (fun _ => K) ξ ω = output p g T ξ := by
  erw [execute_eq_of_answer_eq O g hO]
  unfold method
  erw [QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ hK, QueryPlan.eval_map, eval_outerPlan]
  rfl

end LongTails.Proofs.EmpiricalProximalExecution
