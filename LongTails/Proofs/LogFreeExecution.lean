import LongTails.Proofs.LogFreeStepGood
import LongTails.Proofs.EnergyHessianExecution

namespace LongTails.Proofs.LogFreeExecution

open OracleTemplate OracleTemplate.QueryPlan LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LogFreeProxNewton
open LongTails.Proofs.LogFreeTransition LongTails.Proofs.LogFreeInvariant
  LongTails.Proofs.LogFreeStepGood LongTails.Proofs.EnergyHessianExecution
  LongTails.Proofs.LogFreeParameters LongTails.Proofs.LogFreeGeometry

variable (p : Params) (f : p.E → ℝ)

noncomputable def states (st : State p.E) (t : ℕ) : State p.E := (transition p f)^[t] st

lemma states_succ (st : State p.E) (t : ℕ) :
    states p f st (t + 1) = transition p f (states p f st t) :=
  Function.iterate_succ_apply' _ _ _

lemma loop_eval (st : State p.E) (t : ℕ) :
    (loop p t st).eval (replies p f) = states p f st t := by
  induction t generalizing st with
  | zero => rfl
  | succ t ih =>
    simp only [loop, id_eq, eval_bind, ih]
    exact (Function.iterate_succ_apply _ _ _).symm

lemma step_counts (g : Fin 2 × p.E → Reply p.E) (st : State p.E) (i : Fin 2) :
    counts g (step p st) i = if i = 0 then 6 else 2 := by
  fin_cases i <;> simp [step, counts]

lemma loop_counts (g : Fin 2 × p.E → Reply p.E) (st : State p.E) (t : ℕ) (i : Fin 2) :
    counts g (loop p t st) i = (if i = 0 then 6 else 2) * t := by
  induction t generalizing st with
  | zero => simp [loop, counts]
  | succ t ih =>
    simp only [loop, id_eq, counts_bind, step_counts, ih]
    ring

lemma plan_counts (g : Fin 2 × p.E → Reply p.E) (i : Fin 2) :
    counts g (plan p) i = 1 + (if i = 0 then 6 else 2) * steps p := by
  fin_cases i <;> simp [plan, counts, counts_map, loop_counts]

noncomputable def start : State p.E :=
  initial p (replies p f (0, p.x0)) (replies p f (1, p.x0))

lemma start_eq : start p f = ⟨p.x0, f p.x0, exact p f p.x0, false, 0, false, p.x0⟩ := by
  simp only [start, initial, reply_value, reply_hessian]
  rfl

lemma plan_eval : (plan p).eval (replies p f) = finish (states p f (start p f) (steps p)) := by
  simp only [plan, eval, eval_map, start, loop_eval]

section Accuracy

variable (hp : spec.valid p) (ha : Admissible p f)
include hp ha

omit hp ha in
lemma start_good : Good p f 0 (start p f) := by
  rw [start_eq]
  refine ⟨rfl, rfl, ?_, le_rfl, ?_, fun h => by simp at h, fun h => by simp at h⟩
  · show regF f (weight p) p.x0 p.x0 ≤ f p.x0
    simp [regF]
  · show ‖p.x0 - p.x0‖ ≤ 2 * scale p * ((0 : ℕ) : ℝ)
    simp

omit ha in
lemma start_measure : potential p f (start p f) =
    phaseWeight * p.Δ / threshold p + finalLevel p + (2 + (2 ^ 14 + 1)) := by
  rw [start_eq, global_measure p f (st := ⟨p.x0, f p.x0, exact p f p.x0, false, 0, false, p.x0⟩)
    rfl rfl]
  simp only [exact_x]
  rw [restart_term p f hp]
  ring

omit ha in
lemma start_measure_lt : potential p f (start p f) < steps p := by
  rw [start_measure p f hp]
  have hS := complexity_eq p hp
  have hu := unit_pos p hp
  have hΓ := logArgument_ge p hp
  have hlog : 0 < Real.log (logArgument p) := Real.log_pos (by linarith)
  have hS0 : 0 ≤ complexity p := by rw [hS]; exact div_nonneg hp.2.1.le hu.le
  have hq : phaseWeight * p.Δ / threshold p = (2 ^ 14 + 3) * 4096 * complexity p := by
    rw [hS]; unfold phaseWeight threshold; field_simp
  have hK : (finalLevel p : ℝ) ≤ 21 + 2 * Real.log (logArgument p) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 20 + 2 * Real.log (logArgument p) by linarith)
    unfold finalLevel; linarith
  have hN : 2 ^ 27 * (1 + complexity p + Real.log (logArgument p)) ≤ (steps p : ℝ) := by
    unfold steps; exact Nat.le_ceil _
  rw [hq]
  nlinarith

lemma states_good : ∀ t, t ≤ steps p →
    Good p f t (states p f (start p f) t) ∧
      ((states p f (start p f) t).done = true ∨
        potential p f (states p f (start p f) t) ≤ potential p f (start p f) - t) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨start_good p f, Or.inr (by simp [states])⟩
  | succ t ih =>
    intro ht
    obtain ⟨hg, hor⟩ := ih (by omega)
    rw [states_succ]
    cases hd : (states p f (start p f) t).done
    · obtain ⟨hg', hmeas⟩ := step_progress p f hp ha (by omega) hg hd
      refine ⟨hg', ?_⟩
      rcases hmeas with h | h
      · exact Or.inl h
      · right
        rcases hor with h' | h'
        · rw [hd] at h'; exact absurd h' (by simp)
        · push_cast; linarith
    · obtain ⟨heq, hg'⟩ := step_done p f hp hg hd
      rw [heq]
      exact ⟨hg', Or.inl hd⟩

lemma plan_accuracy : ‖gradient f ((plan p).eval (replies p f))‖ ≤ p.ε := by
  rw [plan_eval]
  obtain ⟨hg, hor⟩ := states_good p f hp ha (steps p) le_rfl
  have hdone : (states p f (start p f) (steps p)).done = true := by
    rcases hor with h | h
    · exact h
    · exfalso
      have hnn := measure_nonneg p f hp ha hg
      have hlt := start_measure_lt p f hp
      linarith
  unfold finish
  rw [ite_eq_left hdone]
  exact hg.out hdone

end Accuracy

end LongTails.Proofs.LogFreeExecution
