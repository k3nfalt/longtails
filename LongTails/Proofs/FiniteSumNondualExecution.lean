import LongTails.Algorithms.FiniteSumNondual
import LongTails.Proofs.FiniteSumNondualProxFeasibility

open MeasureTheory

namespace LongTails.Proofs.FiniteSumNondualExecution

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual
open FiniteSumNondualProxFeasibility
open OracleTemplate
open OracleTemplate.ComponentEnvelope (Program)

lemma feasiblePoint_val (p : Params) (x : Point p) (hx : x ∈ domain p) :
    (feasiblePoint p x).val = x := by simp only [feasiblePoint, dite_eq_left hx]

lemma adaptProgram_eval (p : Params) {U : Type*} {good : U → Prop}
    {program : Program (Fin p.n × Point p) (Point p) U}
    (h : Checked (fun q => q.2 ∈ domain p) good program) (g : Fin p.n × Point p → Point p) :
    Program.eval (fun q : Fin p.n × Feasible p => g (q.1, q.2.val)) (adaptProgram p program) =
      Program.eval g program := by
  apply mapQueries_eval h
  intro q hq
  simp only [feasiblePoint_val p q.2 hq]

lemma adaptProgram_cost (p : Params) {U : Type*} {good : U → Prop}
    {program : Program (Fin p.n × Point p) (Point p) U}
    (h : Checked (fun q => q.2 ∈ domain p) good program) (g : Fin p.n × Point p → Point p) :
    Program.cost (fun q : Fin p.n × Feasible p => g (q.1, q.2.val)) (adaptProgram p program) =
      Program.cost g program := by
  apply mapQueries_cost h
  intro q hq
  simp only [feasiblePoint_val p q.2 hq]

lemma execute_program (p : Params) {Seed : Type} [MeasurableSpace Seed]
    (law : ProbabilityMeasure Seed)
    (plan : Seed → Program (Fin p.n × Point p) (Point p) (Point p))
    (oracle : Oracle (Fin p.n × Feasible p) (Point p)) (g : Fin p.n × Point p → Point p)
    (hg : ∀ history query seed, oracle.answer history (0, query) seed = g (query.1, query.2.val))
    (K : ℕ) (seed : Seed) (oracleSeed : (k : ℕ) → oracle.Seed k)
    (hchecked : Checked (fun q => q.2 ∈ domain p) (fun x => x ∈ domain p) (plan seed))
    (hcost : Program.cost g (plan seed) ≤ K) :
    (output p law plan oracle K seed oracleSeed).val = Program.eval g (plan seed) := by
  let response := fun q : Fin p.n × Feasible p => g (q.1, q.2.val)
  have hc : Program.cost response ((adaptProgram p (plan seed)).map (feasiblePoint p)) ≤ K := by
    rw [Program.cost_map, adaptProgram_cost p hchecked g]
    exact hcost
  have he : output p law plan oracle K seed oracleSeed = feasiblePoint p (Program.eval g (plan seed)) := by
    unfold output
    erw [execute_eq_of_answer_eq oracle response hg,
      execute_iterate response (programAlgorithm p law plan) K seed]
    change Program.output (feasiblePoint p 0)
      ((fun state : Program (Fin p.n × Feasible p) (Point p) (Feasible p) =>
        state.update (response (state.query (0, feasiblePoint p 0))))^[K]
          ((adaptProgram p (plan seed)).map (feasiblePoint p))) = _
    rw [Program.iterate_of_cost_le response (0, feasiblePoint p 0) K _ hc,
      Program.output, Program.eval_map, adaptProgram_eval p hchecked g]
  rw [he, feasiblePoint_val p _ (checked_eval hchecked g)]

end LongTails.Proofs.FiniteSumNondualExecution
