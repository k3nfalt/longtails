import LongTails.Algorithms.FirstFitGradientDescent
import LongTails.Proofs.Execution

open OracleTemplate
open LongTails.Algorithms.FirstFitGradientDescent

namespace LongTails.Proofs.FirstFitGradientExecution

variable {E : Type}

lemma freeze_or_follow (F : E → E) (fit : E → Bool) (x : E) (k : ℕ) :
    let T := fun z => if fit z then z else F z
    fit (T^[k] x) = true ∨ T^[k] x = F^[k] x := by
  intro T
  induction k with
  | zero => exact Or.inr rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' F]
    by_cases h : fit (T^[k] x) = true
    · left
      simp [T, h]
    · right
      have hn : fit (T^[k] x) = false := Bool.eq_false_iff.mpr h
      simpa [T, hn] using congrArg F (ih.resolve_left h)

lemma return_fit (F : E → E) (fit : E → Bool) (x : E) {k K : ℕ} (hk : k ≤ K)
    (hs : fit (F^[k] x) = true) :
    let T := fun z => if fit z then z else F z
    fit (T^[K] x) = true := by
  intro T
  have hf : fit (T^[k] x) = true := by
    rcases freeze_or_follow F fit x k with h | h
    · exact h
    · rwa [h]
  have hfixed : T (T^[k] x) = T^[k] x := by simp [T, hf]
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm k j, Function.iterate_add_apply, Function.IsFixedPt.iterate hfixed j]
  exact hf

variable [Add E] [SMul ℝ E]

lemma execute_first_fit (g : E → E) (fit : E → Bool) (o : Oracle E (E × Bool))
    (hO : ∀ h q ξ, o.answer h (0,q) ξ = (g q,fit q))
    (η : ℝ) (x : E) {k K : ℕ} (hk : k ≤ K) (hfit : fit ((fun z => z + η • g z)^[k] x) = true)
    (ξ : (k : ℕ) → o.Seed k) :
    fit (output x η o K ξ) = true := by
  unfold output
  have he := (execute_eq_of_answer_eq o (fun q => (g q,fit q)) hO (algorithm x η) K () ξ).trans
    (execute_iterate (fun q => (g q,fit q)) (algorithm x η) K ())
  rw [he]
  exact return_fit (fun z => z + η • g z) fit x hk hfit

end LongTails.Proofs.FirstFitGradientExecution
