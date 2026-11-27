import LongTails.Template
import Mathlib.Tactic

namespace LongTails.Proofs.SlidingLowerRun

open OracleTemplate

open private _run from LongTails.Template

variable {Query Reply Output : Type*} {n : ℕ}

noncomputable def brun (A : Algorithm Query Reply Output n) (response : ℕ → Fin n × Query → Reply) :
    ℕ → (Fin n → ℕ) → A.State → ℕ → A.State
  | 0, _, s, _ => s
  | f + 1, rem, s, t =>
      if rem (A.query s).1 = 0 then s
      else brun A response f (Function.update rem (A.query s).1 (rem (A.query s).1 - 1))
        (A.update s (response t (A.query s))) (t + 1)

lemma execute_eq_brun (O : Oracle Query Reply n) (A : Algorithm Query Reply Output n)
    (budget : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (response : ℕ → Fin n × Query → Reply)
    (h : ∀ history q, O.answer history q (ξ history.length) = response history.length q) :
    execute O A budget seed ξ =
      A.output (brun A response (∑ i, budget i) budget (A.initial seed) 0) := by
  unfold execute executeWithTrace
  generalize (∑ i, budget i) = fuel
  generalize A.initial seed = s
  have key : ∀ (fuel : ℕ) (history : List ((Fin n × Query) × Reply)) (rem : Fin n → ℕ)
      (s : A.State),
      (_run (fun history query => O.answer history query (ξ history.length)) A fuel
        history rem s).1 = A.output (brun A response fuel rem s history.length) := by
    intro fuel
    induction fuel with
    | zero => intro history rem s; rfl
    | succ fuel ih =>
        intro history rem s
        unfold _run
        simp only [brun]
        split_ifs with hz
        · rfl
        · rw [ih, h]
          simp
  simpa using key fuel [] budget s

def calls (A : Algorithm Query Reply Output n) (response : ℕ → Fin n × Query → Reply)
    (i : Fin n) : ℕ → (Fin n → ℕ) → A.State → ℕ → ℕ
  | 0, _, _, _ => 0
  | f + 1, rem, s, t =>
      if rem (A.query s).1 = 0 then 0
      else (if (A.query s).1 = i then 1 else 0) +
        calls A response i f (Function.update rem (A.query s).1 (rem (A.query s).1 - 1))
          (A.update s (response t (A.query s))) (t + 1)

lemma calls_le (A : Algorithm Query Reply Output n) (response : ℕ → Fin n × Query → Reply)
    (i : Fin n) (fuel : ℕ) (rem : Fin n → ℕ) (s : A.State) (t : ℕ) :
    calls A response i fuel rem s t ≤ rem i := by
  induction fuel generalizing rem s t with
  | zero => simp [calls]
  | succ fuel ih =>
      simp only [calls]
      split_ifs with hz hi
      · exact Nat.zero_le _
      · have := ih (Function.update rem (A.query s).1 (rem (A.query s).1 - 1))
          (A.update s (response t (A.query s))) (t + 1)
        subst hi
        rw [Function.update_self] at this
        omega
      · have := ih (Function.update rem (A.query s).1 (rem (A.query s).1 - 1))
          (A.update s (response t (A.query s))) (t + 1)
        rw [Function.update_of_ne (Ne.symm hi)] at this
        omega

end LongTails.Proofs.SlidingLowerRun
