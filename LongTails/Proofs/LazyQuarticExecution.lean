import LongTails.Algorithms.LazyQuarticMetric
import LongTails.Proofs.QuarticStageExecution
import LongTails.Proofs.ReshufflingExecution

namespace LongTails.Proofs.LazyQuarticExecution

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Algorithms.QuarticMetricStage (Reply)
open LongTails.Proofs.EnergyHessianExecution

noncomputable def refreshNeeded (p : Params) (st : State p) : Bool := by
  classical
  exact decide (p.ε < ‖st.point.gradient‖ ∧ radius p / 4 < ‖st.coordinates (st.point.x - st.snapshot)‖)

lemma refresh_point (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) :
    ((refresh p st).eval g).point = st.point := by
  classical
  simp only [refresh]
  split <;> rfl

lemma refresh_counts (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (i : Fin 2) :
    counts g (refresh p st) i = if refreshNeeded p st then (if i = 1 then 1 else 0)
      else (if i = 0 then 1 else 0) := by
  classical
  simp only [refresh, refreshNeeded]
  split <;> simp_all [counts]

lemma step_hessian_calls (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) :
    counts g (step p st) 1 = if refreshNeeded p st then 1 else 0 := by
  classical
  simp only [step, counts_bind]
  split
  · rw [counts_map, QuarticStageExecution.plan_counts, refresh_counts]
    simp
  · rw [QuarticStageExecution.counts_cast, counts_map,
      QuarticStageExecution.traverse_counts g _ 1 (d := 0) (by intro j; simp [counts]), refresh_counts]
    simp

lemma step_total_calls (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) :
    counts g (step p st) 0 + counts g (step p st) 1 = 2 * innerSteps p + 8 := by
  have hh := counts_sum g (step p st)
  simpa only [Fin.sum_univ_two] using hh

lemma step_ordinary_calls (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) :
    counts g (step p st) 0 ≤ 2 * innerSteps p + 8 := by
  have hh := step_total_calls p g st
  omega

noncomputable def states (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ) : State p :=
  (fun s => (step p s).eval g)^[t] st

lemma states_zero (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) : states p g st 0 = st := rfl

lemma states_succ (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ) :
    states p g st (t + 1) = (step p (states p g st t)).eval g := Function.iterate_succ_apply' _ _ _

lemma states_succ_shift (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ) :
    states p g st (t + 1) = states p g ((step p st).eval g) t := Function.iterate_succ_apply _ _ _

lemma loop_eval (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ) :
    (loop p t st).eval g = states p g st t := by
  induction t generalizing st with
  | zero => rfl
  | succ t ih =>
    simp only [loop, id_eq, eval_bind, ih, states_succ_shift]

lemma loop_ordinary_calls (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ) :
    counts g (loop p t st) 0 ≤ (2 * innerSteps p + 8) * t := by
  induction t generalizing st with
  | zero => simp [loop, counts]
  | succ t ih =>
    simp only [loop, id_eq, counts_bind]
    have hh := step_ordinary_calls p g st
    have ht := ih ((step p st).eval g)
    nlinarith

lemma loop_hessian_calls (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) (t : ℕ) :
    counts g (loop p t st) 1 =
      ∑ i ∈ Finset.range t, if refreshNeeded p (states p g st i) then 1 else 0 := by
  induction t generalizing st with
  | zero => simp [loop, counts]
  | succ t ih =>
    rw [loop, id_eq, counts_bind, step_hessian_calls, ih, Finset.sum_range_succ']
    simp only [states_zero, states_succ_shift]
    exact Nat.add_comm _ _

lemma step_inactive (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p)
    (hi : ‖st.point.gradient‖ ≤ p.ε) : (step p st).eval g = st := by
  classical
  have hn : ¬p.ε < ‖st.point.gradient‖ := not_lt.mpr hi
  simp only [step, eval_bind]
  have hr : (refresh p st).eval g = st := by simp [refresh, hn, eval]
  rw [hr]
  simp only [hn, ↓reduceIte, OracleTemplate.RandomReshuffling.eval_cast, eval_map]

lemma step_coordinates (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) :
    ((step p st).eval g).coordinates = ((refresh p st).eval g).coordinates := by
  classical
  simp only [step, eval_bind]
  split
  · rw [eval_map]
  · rw [OracleTemplate.RandomReshuffling.eval_cast, eval_map]

lemma step_snapshot (p : Params) (g : Fin 2 × p.E → Reply p.E) (st : State p) :
    ((step p st).eval g).snapshot = ((refresh p st).eval g).snapshot := by
  classical
  simp only [step, eval_bind]
  split
  · rw [eval_map]
  · rw [OracleTemplate.RandomReshuffling.eval_cast, eval_map]

end LongTails.Proofs.LazyQuarticExecution
