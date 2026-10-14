import LongTails.Proofs.ReshuffledEpoch
import LongTails.Proofs.ReshuffledAnchorCoupling

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledExchange

open ReshuffledConvex
open LongTails.Setups.ReshuffledSmoothConvex

variable {n K : ℕ}

noncomputable def swapOrder (k : Fin K) (i j : Fin n) (s : Orders n K) : Orders n K :=
  Function.update s k ((Equiv.swap i j).trans (s k))

lemma swapOrder_at (k : Fin K) (i j : Fin n) (s : Orders n K) (a : Fin n) :
    swapOrder k i j s k a = s k (Equiv.swap i j a) := by
  unfold swapOrder
  erw [Function.update_self]
  rfl

lemma swapOrder_other (k l : Fin K) (h : l ≠ k) (i j : Fin n) (s : Orders n K) :
    swapOrder k i j s l = s l := by
  exact Function.update_of_ne h _ _

lemma swapOrder_involutive (k : Fin K) (i j : Fin n) :
    Function.Involutive (swapOrder k i j) := by
  intro s
  funext l
  by_cases h : l = k
  · subst l
    apply Equiv.ext
    intro a
    simp [swapOrder_at, Equiv.swap_apply_self]
  · rw [swapOrder_other _ _ h, swapOrder_other _ _ h]

noncomputable def swapEquiv (k : Fin K) (i j : Fin n) : Orders n K ≃ Orders n K :=
  (swapOrder_involutive k i j).toPerm

lemma sum_swap (k : Fin K) (i j : Fin n) (F : Orders n K → ℝ) :
    ∑ s, F (swapOrder k i j s) = ∑ s, F s := by
  exact Equiv.sum_comp (swapEquiv k i j) F

lemma sum_swap_label (k : Fin K) (i j : Fin n) (F : Fin n → Orders n K → ℝ) :
    ∑ s, F (s k j) s = ∑ s, F (s k i) (swapOrder k i j s) := by
  have h := sum_swap k i j (fun s => F (s k j) s)
  simpa [swapOrder_at] using h.symm

lemma sum_component_swap (k : Fin K) (i : Fin n) (F : Fin n → Orders n K → ℝ) :
    ∑ s : Orders n K, ∑ a : Fin n, F a s =
      ∑ j : Fin n, ∑ s : Orders n K, F (s k i) (swapOrder k i j s) := by
  calc
    ∑ s : Orders n K, ∑ a : Fin n, F a s =
        ∑ s : Orders n K, ∑ j : Fin n, F (s k j) s := by
      apply sum_congr rfl
      intro s _
      exact (Equiv.sum_comp (s k) (fun a => F a s)).symm
    _ = ∑ j : Fin n, ∑ s : Orders n K, F (s k j) s := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      exact sum_swap_label k i j F

lemma centered_exchange (k : Fin K) (i : Fin n) (F : Fin n → Orders n K → ℝ) :
    (∑ s : Orders n K, ∑ a : Fin n, F a s) -
        n * ∑ s : Orders n K, F (s k i) s =
      ∑ j : Fin n, ∑ s : Orders n K,
        (F (s k i) (swapOrder k i j s) - F (s k i) s) := by
  rw [sum_component_swap k i F]
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma sum_label_eq_of_invariant {X : Type*} (k : Fin K) (i j : Fin n)
    (x : Orders n K → X) (f : Fin n → X → ℝ)
    (hinv : ∀ s, x (swapOrder k i j s) = x s) :
    ∑ s : Orders n K, f (s k i) (x s) = ∑ s : Orders n K, f (s k j) (x s) := by
  have h := sum_swap_label k i j (fun a s => f a (x s))
  simpa only [hinv] using h.symm

lemma sum_label_mean_of_invariant {X : Type*} (k : Fin K) (i : Fin n)
    (x : Orders n K → X) (f : Fin n → X → ℝ)
    (hinv : ∀ j s, x (swapOrder k i j s) = x s) :
    n * ∑ s : Orders n K, f (s k i) (x s) =
      ∑ s : Orders n K, ∑ a : Fin n, f a (x s) := by
  rw [sum_component_swap k i (fun a s => f a (x s))]
  simp only [hinv, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end OracleTemplate.ReshuffledExchange
