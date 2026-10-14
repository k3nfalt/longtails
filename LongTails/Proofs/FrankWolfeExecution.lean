import LongTails.Algorithms.ShortStepFrankWolfe
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate.FrankWolfe

open StochasticGradient HeavyTailedMarkovGradient
open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_short_step_even (O : Oracle (E ⊕ E) E) (L : ℝ) (x0 : E)
    (ξ : (k : ℕ) → O.Seed k) (x : ℕ → E) (hzero : x 0 = x0)
    (hstep : ∀ k, x (k + 1) = shortStep L (x k)
      (O.answer (2 * k) (0, (Sum.inl (x k))) (ξ (2 * k)))
      (O.answer (2 * k + 1)
        (0, (Sum.inr (O.answer (2 * k) (0, (Sum.inl (x k))) (ξ (2 * k))))) (ξ (2 * k + 1))))
    (n : ℕ) : execute O (shortStepFrankWolfe L x0) (fun _ => (2 * n)) () ξ = x n := by
  let A := shortStepFrankWolfe L x0
  let step := fun k s => A.update s (O.answer k (A.query s) (ξ k))
  have hs : ∀ k, advance step (2 * k) 0 (A.initial ()) = (false, x k, 0) := by
    intro k
    induction k with
    | zero => simpa [advance, A, shortStepFrankWolfe] using hzero.symm
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, advance_add, Nat.zero_add, ih]
      simp only [advance, step, A, shortStepFrankWolfe, Bool.false_eq_true,
        ite_false, ite_true]
      rw [hstep]
  erw [execute_advance]
  change A.output (advance step (2 * n) 0 (A.initial ())) = _
  rw [hs]
  rfl

lemma execute_short_step_odd (O : Oracle (E ⊕ E) E) (L : ℝ) (x0 : E)
    (ξ : (k : ℕ) → O.Seed k) (x : ℕ → E) (hzero : x 0 = x0)
    (hstep : ∀ k, x (k + 1) = shortStep L (x k)
      (O.answer (2 * k) (0, (Sum.inl (x k))) (ξ (2 * k)))
      (O.answer (2 * k + 1)
        (0, (Sum.inr (O.answer (2 * k) (0, (Sum.inl (x k))) (ξ (2 * k))))) (ξ (2 * k + 1))))
    (n : ℕ) : execute O (shortStepFrankWolfe L x0) (fun _ => (2 * n + 1)) () ξ =
      x n := by
  let A := shortStepFrankWolfe L x0
  let step := fun k s => A.update s (O.answer k (A.query s) (ξ k))
  have hs : ∀ k, advance step (2 * k) 0 (A.initial ()) = (false, x k, 0) := by
    intro k
    induction k with
    | zero => simpa [advance, A, shortStepFrankWolfe] using hzero.symm
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, advance_add, Nat.zero_add, ih]
      simp only [advance, step, A, shortStepFrankWolfe, Bool.false_eq_true,
        ite_false, ite_true]
      rw [hstep]
  erw [execute_advance]
  change A.output (advance step (2 * n + 1) 0 (A.initial ())) = _
  rw [advance_add, Nat.zero_add, hs]
  rfl

lemma execute_short_step (O : Oracle (E ⊕ E) E) (L : ℝ) (x0 : E)
    (ξ : (k : ℕ) → O.Seed k) (x : ℕ → E) (hzero : x 0 = x0)
    (hstep : ∀ k, x (k + 1) = shortStep L (x k)
      (O.answer (2 * k) (0, (Sum.inl (x k))) (ξ (2 * k)))
      (O.answer (2 * k + 1)
        (0, (Sum.inr (O.answer (2 * k) (0, (Sum.inl (x k))) (ξ (2 * k))))) (ξ (2 * k + 1))))
    (K : ℕ) : execute O (shortStepFrankWolfe L x0) (fun _ => K) () ξ = x (K / 2) := by
  rcases Nat.mod_two_eq_zero_or_one K with h | h
  · have hK : 2 * (K / 2) = K := by omega
    have he := execute_short_step_even O L x0 ξ x hzero hstep (K / 2)
    rw [hK] at he
    exact he
  · have hK : 2 * (K / 2) + 1 = K := by omega
    have he := execute_short_step_odd O L x0 ξ x hzero hstep (K / 2)
    rw [hK] at he
    exact he

end OracleTemplate.FrankWolfe
