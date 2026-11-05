import LongTails.Algorithms.BilevelAccelerated
import LongTails.Proofs.AcceleratedConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.BilevelExecution

open OracleTemplate LongTails.Algorithms.BilevelAccelerated LongTails.Setups.HigherSmoothBilevel

lemma eval_repeatPlan {Q R S : Type*} {c : ℕ} (g : Q → R)
    (body : S → QueryPlan Q R S c) (n : ℕ) (s : S) :
    QueryPlan.eval g (repeatPlan n body s) = (fun s => QueryPlan.eval g (body s))^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [repeatPlan, QueryPlan.eval_bind, ih, Function.iterate_succ_apply]

lemma eval_innerSteps (p : Params) (g : p.X × p.Y → Reply p) (x : p.X)
    (lam : ℝ) (m : ℕ) (s : ℕ × p.Y × p.Y) :
    QueryPlan.eval g (innerSteps p x lam m s) =
      (fun s => (Gradient.accelerated (2 * p.L, p.y0)).update s
        (lowerReply p lam (g (x, Gradient.acceleratedQuery s))))^[m] s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih => simp only [innerSteps, QueryPlan.eval, ih, Function.iterate_succ_apply]

lemma eval_innerEpoch (p : Params) (g : p.X × p.Y → Reply p) (x : p.X)
    (lam : ℝ) (m : ℕ) (y : p.Y) :
    QueryPlan.eval g (innerEpoch p x lam m y) =
      execute { answer := fun _ q _ => lowerReply p lam (g (x, q.2)) }
        (Gradient.accelerated (2 * p.L, y)) (fun _ => m) := by
  refine Eq.trans ?_ (execute_iterate (fun u => lowerReply p lam (g (x, u)))
    (Gradient.accelerated (2 * p.L, y)) m ()).symm
  unfold innerEpoch
  simp only [QueryPlan.eval_map, eval_innerSteps]
  rfl

lemma eval_innerSolve (p : Params) (g : p.X × p.Y → Reply p) (t : Tuning)
    (x : p.X) (lam : ℝ) :
    QueryPlan.eval g (innerSolve p t x lam) =
      (fun y => execute { answer := fun _ q _ => lowerReply p lam (g (x, q.2)) }
        (Gradient.accelerated (2 * p.L, y)) (fun _ => t.m))^[t.J] p.y0 := by
  simp only [innerSolve, eval_repeatPlan, eval_innerEpoch]

lemma eval_estimate (p : Params) (g : p.X × p.Y → Reply p) (t : Tuning) (x : p.X) :
    QueryPlan.eval g (estimate p t x) =
      let y := QueryPlan.eval g (innerSolve p t x t.lam)
      let z := QueryPlan.eval g (innerSolve p t x 0)
      upperReply p (g (x, y)).2.2.1 +
        t.lam • (upperReply p (g (x, y)).2.2.2 - upperReply p (g (x, z)).2.2.2) := by
  unfold estimate
  simp only [QueryPlan.eval_bind, QueryPlan.eval]

lemma eval_outputPlan (p : Params) (g : p.X × p.Y → Reply p) :
    QueryPlan.eval g (outputPlan p) =
      ((fun s => advance p (tuning p) s (QueryPlan.eval g
        (estimate p (tuning p) (context p (tuning p) s))))^[(tuning p).N] (initial p.x0)).result := by
  simp only [outputPlan, QueryPlan.eval_map, eval_repeatPlan, outerStep]

end LongTails.Proofs.BilevelExecution
