import LongTails.Setups.SelfConcordantBFGS
import LongTails.Proofs.ExecutionHistory

namespace LongTails.Proofs.SelfConcordantBFGSExecution

open OracleTemplate LongTails.Setups.SelfConcordantBFGS
open StochasticGradient (advance)

lemma advance_succ_call {S : Type*} (step : ℕ → S → S) :
    ∀ (n c : ℕ) (s : S), advance step (n + 1) c s = step (c + n) (advance step n c s) := by
  intro n
  induction n with
  | zero => intro c s; rfl
  | succ n ih =>
    intro c s
    rw [advance, ih (c + 1) (step c s), advance]
    congr 1
    omega

lemma advance_succ_zero {S : Type*} (step : ℕ → S → S) :
    ∀ (n : ℕ) (s : S), advance step (n + 1) 0 s = step n (advance step n 0 s) := by
  intro n s
  have h := advance_succ_call step n 0 s
  rw [zero_add] at h
  exact h

variable (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1) (ξ : (k : ℕ) → O.Seed k)

noncomputable def step : ℕ → State q.d → State q.d := fun k st =>
  (bfgs q.x0 q.B0).update st (executeAnswerAt O (bfgs q.x0 q.B0) () ξ k ((bfgs q.x0 q.B0).query st))

noncomputable def run (n : ℕ) : State q.d :=
  advance (step q O ξ) (n + 1) 0 ((bfgs q.x0 q.B0).initial ())

noncomputable def answer (n : ℕ) : ℝ × Vec q.d :=
  executeAnswerAt O (bfgs q.x0 q.B0) () ξ (n + 1)
    (0, ((run q O ξ n).x, direction (run q O ξ n).B (run q O ξ n).g))

lemma run_zero : run q O ξ 0 =
    ⟨q.x0, (executeAnswerAt O (bfgs q.x0 q.B0) () ξ 0 (0, (q.x0, 0))).2, q.B0, true⟩ := rfl

lemma run_succ_step (n : ℕ) : run q O ξ (n + 1) = step q O ξ (n + 1) (run q O ξ n) :=
  advance_succ_zero (step q O ξ) (n + 1) _

lemma run_started (n : ℕ) : (run q O ξ n).started = true := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [run_succ_step]
    simp only [step, bfgs]
    split <;> rfl

lemma run_succ (n : ℕ) : run q O ξ (n + 1) =
    ⟨(run q O ξ n).x + (answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g,
      (answer q O ξ n).2,
      LongTails.Setups.LinearPredictorBFGS.bfgsUpdate (run q O ξ n).B
        ((answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g)
        ((answer q O ξ n).2 - (run q O ξ n).g), true⟩ := by
  have hs := run_started q O ξ n
  rw [run_succ_step]
  simp only [step, bfgs, hs, ↓reduceIte, answer]

lemma execute_eq_run (K : ℕ) :
    execute O (bfgs q.x0 q.B0) (fun _ => K + 1) () ξ = (run q O ξ K).x := by
  erw [execute_advance_history]
  rfl

lemma answer_spec (P : ℝ × Vec q.d → Vec q.d → Vec q.d → Prop)
    (h : ∀ history x v seed, P (O.answer history (0, (x, v)) seed) x v) (n : ℕ) :
    P (answer q O ξ n) (run q O ξ n).x (direction (run q O ξ n).B (run q O ξ n).g) :=
  h _ _ _ _

lemma answer0_spec (P : ℝ × Vec q.d → Vec q.d → Vec q.d → Prop)
    (h : ∀ history x v seed, P (O.answer history (0, (x, v)) seed) x v) :
    P (executeAnswerAt O (bfgs q.x0 q.B0) () ξ 0 (0, (q.x0, 0))) q.x0 0 :=
  h _ _ _ _

end LongTails.Proofs.SelfConcordantBFGSExecution
