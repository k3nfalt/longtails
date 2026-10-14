import LongTails.Proofs.ReshufflingExecution
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.RandomReshuffling

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

lemma pass_map {J : Type*} (g : I → E → E) (η : ℝ) (f : J → I) (w : List J) (x : E) :
    pass g η (w.map f) x = pass (fun j => g (f j)) η w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => exact ih (x - η • g (f i) x)

lemma pass_translate (g c : I → E → E) (η : ℝ) (w : List I) (z x : E)
    (hg : ∀ i y, g i (y + z) = c i y) :
    pass g η w (x + z) = pass c η w x + z := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    rw [pass, pass, hg]
    rw [show x + z - η • c i x = (x - η • c i x) + z by abel, ih]

lemma epochs_translate (g c : I → E → E) (η : ℝ) (orders : List (List I)) (z x : E)
    (hg : ∀ i y, g i (y + z) = c i y) :
    epochs g η orders (x + z) = epochs c η orders x + z := by
  induction orders generalizing x with
  | nil => rfl
  | cons w orders ih => rw [epochs, epochs, pass_translate g c η w z x hg, ih]

lemma epochs_sum_energy {n : ℕ} (g : Fin n → E → E) (η : ℝ) (V : E → ℝ)
    {r B : ℝ} (hr : 0 ≤ r)
    (hstep : ∀ x, (∑ π : Equiv.Perm (Fin n), V (pass g η (List.ofFn π) x)) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (r * V x + (1 - r) * B))
    (K : ℕ) (x : E) :
    (∑ seed : Fin K → Equiv.Perm (Fin n),
      V (epochs g η (List.ofFn (fun k => List.ofFn (seed k))) x)) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ K *
        (r ^ K * V x + (1 - r ^ K) * B) := by
  classical
  let C : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hC : 0 ≤ C := Nat.cast_nonneg _
  induction K generalizing x with
  | zero => simp [epochs]
  | succ K ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (K + 1) => Equiv.Perm (Fin n))).sum_comp
      (fun seed => V (epochs g η (List.ofFn (fun k => List.ofFn (seed k))) x))]
    change (∑ p : Equiv.Perm (Fin n) × (Fin K → Equiv.Perm (Fin n)),
      V (epochs g η (List.ofFn (fun k => List.ofFn (Fin.cons (α := fun _ : Fin (K + 1) => Equiv.Perm (Fin n)) p.1 p.2 k))) x)) ≤ _
    simp only [Fintype.sum_prod_type, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, epochs]
    change (∑ π : Equiv.Perm (Fin n), ∑ seed : Fin K → Equiv.Perm (Fin n),
      V (epochs g η (List.ofFn (fun k => List.ofFn (seed k))) (pass g η (List.ofFn π) x))) ≤ _
    calc
      _ ≤ ∑ π : Equiv.Perm (Fin n), C ^ K *
          (r ^ K * V (pass g η (List.ofFn π) x) + (1 - r ^ K) * B) :=
        Finset.sum_le_sum (fun π _ => ih (pass g η (List.ofFn π) x))
      _ = C ^ K * (r ^ K * (∑ π : Equiv.Perm (Fin n), V (pass g η (List.ofFn π) x)) +
          C * (1 - r ^ K) * B) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ C ^ K * (r ^ K * (C * (r * V x + (1 - r) * B)) + C * (1 - r ^ K) * B) := by
        gcongr
        exact hstep x
      _ = _ := by change _ = C ^ (K + 1) * _; rw [pow_succ, pow_succ]; ring

end OracleTemplate.RandomReshuffling
