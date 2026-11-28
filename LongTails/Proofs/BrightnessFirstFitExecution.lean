import LongTails.Proofs.BrightnessScaledCoordinates

open OracleTemplate

namespace LongTails.Proofs.BrightnessFirstFitExecution

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Algorithms.BrightnessScaledTwoTap (algorithm output)
open LongTails.Proofs.BrightnessScaledCoordinates
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space)

lemma allowed (p : Params) (η : ℝ) (hη : 0 < η) : family p (algorithm p η) :=
  ⟨id,η,hη,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

lemma fitted_execute (p : Params) (x : Images p) (κ : ℝ) (hR : 0 < p.R)
    (oracle : Oracle (Space p.d) (Reply p.d))
    (hor : ∀ k q seed, oracle.answer k q seed = answer p x q.2)
    (ξ : (k : ℕ) → oracle.Seed k) (N : ℕ)
    (hit : ∃ t ≤ N, Fitted p x (physical p (path p x κ t))) :
    Fitted p x (execute oracle (algorithm p (κ/p.R)) (fun _ => N) () ξ) := by
  classical
  let A := algorithm p (κ/p.R)
  let f : Space p.d → Space p.d := fun θ => A.update θ (answer p x θ)
  let θ := fun k => physical p (path p x κ k)
  have ff (s : Space p.d) : f s = if Fitted p x s then s else s + (κ/p.R) • (answer p x s).descent := by
    simp only [f,A,algorithm,answer,decide_eq_true_eq]
  have alt (k : ℕ) : Fitted p x (f^[k] (start p)) ∨ f^[k] (start p) = θ k := by
    induction k with
    | zero => exact Or.inr (physical_initial p hR).symm
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · left
        rwa [ff,ite_eq_left h]
      · rw [h,ff]
        split_ifs with hfit
        · exact Or.inl hfit
        · exact Or.inr (path_update p x κ hR k).symm
  obtain ⟨k,hk,hfit⟩ := hit
  have good : Fitted p x (f^[k] (start p)) := (alt k).elim id (fun h => h.symm ▸ hfit)
  have keep (j : ℕ) : Fitted p x (f^[k+j] (start p)) := by
    induction j with
    | zero => simpa using good
    | succ j ih =>
      rw [Nat.add_succ,Function.iterate_succ_apply',ff,ite_eq_left ih]
      exact ih
  have EE := (execute_eq_of_answer_eq oracle (answer p x) (fun t q seed => hor t (0,q) seed) A N () ξ).trans (execute_iterate (answer p x) A N ())
  apply (congrArg (Fitted p x) EE).mpr
  change Fitted p x (f^[N] (start p))
  simpa [Nat.add_sub_of_le hk] using keep (N-k)

end LongTails.Proofs.BrightnessFirstFitExecution
