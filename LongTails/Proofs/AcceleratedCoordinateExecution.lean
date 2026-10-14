import LongTails.Algorithms.AcceleratedCoordinate
import LongTails.Proofs.QueryPlan

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

lemma eval_plan (p : Params) (g : Fin p.d × EuclideanSpace ℝ (Fin p.d) → ℝ)
    (K : ℕ) (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
    (choices : Fin K → CoordinateChoice p) :
    QueryPlan.eval g (plan p K s choices) = (run p g s (List.ofFn choices)).1 := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih => simp only [plan, QueryPlan.eval, List.ofFn_succ, run, ih]

lemma execute_acceleratedCoordinate (p : Params)
    (g : Fin p.d × EuclideanSpace ℝ (Fin p.d) → ℝ) (K : ℕ) (seed : Seeds p K) :
    execute { answer := fun _ (_, q) _ => g q } (acceleratedCoordinate p K) (fun _ => K) seed =
      (run p g (p.x0, p.x0) (List.ofFn seed)).1 := by
  unfold acceleratedCoordinate
  erw [QueryPlan.execute_plan, eval_plan]

end OracleTemplate.AcceleratedCoordinate
