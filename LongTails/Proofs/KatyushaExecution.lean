import LongTails.Algorithms.Katyusha
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

noncomputable def answer (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) : Query p → p.E
  | .gradient i x => g (i, x)
  | .prox a z v => prox a z v

lemma eval_fullPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) (snapshot : p.E) :
    QueryPlan.eval (answer p g prox) (fullPlan p snapshot) =
      FiniteSum.fullGradient g snapshot := by
  simp [fullPlan, QueryPlan.eval_map, QueryPlan.eval_traverse,
    QueryPlan.eval, List.sum_ofFn, FiniteSum.fullGradient, answer]

lemma eval_stepPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) (snapshot : p.E) (s : p.E × p.E)
    (full : p.E) (i : Fin p.n) :
    QueryPlan.eval (answer p g prox) (stepPlan p snapshot s full i) =
      advance (tau p) (alpha p) p.L prox snapshot s
        (g (i, mix (tau p) snapshot s) - g (i, snapshot) + full) := by
  rfl

lemma eval_innerPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) (snapshot full : p.E)
    (k : ℕ) (s : p.E × p.E) (samples : Fin k → Fin p.n) :
    QueryPlan.eval (answer p g prox) (innerPlan p snapshot full k s samples) =
      innerRun (tau p) (alpha p) p.L (theta p) g prox snapshot full k s samples := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [innerPlan, QueryPlan.eval_bind, QueryPlan.eval_map,
        eval_stepPlan, ih, innerRun]

lemma eval_epochPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) (s : State p.E)
    (samples : Fin (2 * p.n) → Fin p.n) :
    QueryPlan.eval (answer p g prox) (epochPlan p s samples) =
      epoch (tau p) (alpha p) p.L (theta p) (2 * p.n) g prox s samples := by
  simp only [epochPlan, QueryPlan.eval_bind, QueryPlan.eval_map,
    eval_fullPlan, eval_innerPlan, epoch]

lemma eval_allPlan (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) (S : ℕ) (s : State p.E)
    (samples : Fin S → Fin (2 * p.n) → Fin p.n) :
    QueryPlan.eval (answer p g prox) (allPlan p S s samples) =
      run (tau p) (alpha p) p.L (theta p) (2 * p.n) g prox S s samples := by
  induction S generalizing s with
  | zero => rfl
  | succ S ih => simp only [allPlan, QueryPlan.eval_bind, eval_epochPlan, ih, run]

lemma execute_katyusha (p : Params) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E) (S : ℕ) (seed : Seeds p S) :
    execute { answer := fun _ (_, q) _ => answer p g prox q } (katyusha p S)
        (fun _ => ((4 * (2 * p.n) + 1 * p.n) * S)) seed =
      (run (tau p) (alpha p) p.L (theta p) (2 * p.n) g prox S
        ⟨p.x0, p.x0, p.x0⟩ seed).snapshot := by
  unfold katyusha
  erw [QueryPlan.execute_plan, QueryPlan.eval_map, eval_allPlan]

end OracleTemplate.Katyusha
