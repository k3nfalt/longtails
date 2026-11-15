import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumPairs

variable {n g : ℕ}

def index (h : 2 * g ≤ n) (a : Fin g × Fin 2) : Fin n :=
  ⟨2 * a.1.val + a.2.val, by have h₁ := a.1.isLt; have h₂ := a.2.isLt; omega⟩

lemma index_injective (h : 2 * g ≤ n) : Function.Injective (index h) := by
  intro a b hab
  have he := congrArg Fin.val hab
  have ha := a.2.isLt
  have hb := b.2.isLt
  change 2 * a.1.val + a.2.val = 2 * b.1.val + b.2.val at he
  apply Prod.ext <;> apply Fin.ext <;> omega

noncomputable def paired {V : Type*} [AddCommMonoid V] (h : 2 * g ≤ n)
    (F : Fin g × Fin 2 → V) (i : Fin n) : V :=
  ∑ a : Fin g × Fin 2, if index h a = i then F a else 0

lemma paired_at_index {V : Type*} [AddCommMonoid V] (h : 2 * g ≤ n)
    (F : Fin g × Fin 2 → V) (a : Fin g × Fin 2) : paired h F (index h a) = F a := by
  simp only [paired, (index_injective h).eq_iff]
  simp

lemma paired_outside {V : Type*} [AddCommMonoid V] (h : 2 * g ≤ n)
    (F : Fin g × Fin 2 → V) (i : Fin n) (hi : 2 * g ≤ i.val) : paired h F i = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hne : index h a ≠ i := by
    intro he
    have hh := congrArg Fin.val he
    have h₁ := a.1.isLt
    have h₂ := a.2.isLt
    change 2 * a.1.val + a.2.val = i.val at hh
    omega
  simp only [ite_eq_right hne]

lemma paired_sum {V : Type*} [AddCommMonoid V] (h : 2 * g ≤ n) (F : Fin g × Fin 2 → V) :
    (∑ i : Fin n, paired h F i) = ∑ a : Fin g × Fin 2, F a := by
  simp only [paired]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma index_or_outside (h : 2 * g ≤ n) (i : Fin n) :
    (∃ a : Fin g × Fin 2, index h a = i) ∨ 2 * g ≤ i.val := by
  by_cases hi : i.val < 2 * g
  · left
    refine ⟨(⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩), ?_⟩
    apply Fin.ext
    change 2 * (i.val / 2) + i.val % 2 = i.val
    omega
  · right
    omega

lemma paired_property {V : Type*} [AddCommMonoid V] (h : 2 * g ≤ n)
    (F : Fin g × Fin 2 → V) (P : V → Prop) (hzero : P 0) (hF : ∀ a, P (F a))
    (i : Fin n) : P (paired h F i) := by
  rcases index_or_outside h i with ⟨a, rfl⟩ | hi
  · rw [paired_at_index]
    exact hF a
  · rw [paired_outside h F i hi]
    exact hzero

noncomputable def which (hg : 0 < g) (i : Fin n) : Fin g :=
  if h : i.val < 2 * g then ⟨i.val / 2, by omega⟩ else ⟨0, hg⟩

lemma which_index (hg : 0 < g) (h : 2 * g ≤ n) (a : Fin g × Fin 2) :
    which hg (index h a) = a.1 := by
  have hi : (index h a).val < 2 * g := by
    have h₁ := a.1.isLt
    have h₂ := a.2.isLt
    change 2 * a.1.val + a.2.val < 2 * g
    omega
  simp only [which, dite_eq_left hi]
  apply Fin.ext
  change (2 * a.1.val + a.2.val) / 2 = a.1.val
  have h₂ := a.2.isLt
  omega

lemma paired_sum_real (h : 2 * g ≤ n) (F : Fin g × Fin 2 → ℝ) :
    (∑ i : Fin n, paired h F i) = ∑ j : Fin g, (F (j, 0) + F (j, 1)) := by
  rw [paired_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  exact Fin.sum_univ_two _

noncomputable def ownerQuery (g : ℕ) (i : Fin n) : Fin (g + 1) :=
  if h : i.val < 2 * g then ⟨i.val / 2, by omega⟩ else Fin.last g

lemma ownerQuery_index (h : 2 * g ≤ n) (a : Fin g × Fin 2) :
    ownerQuery g (index h a) = a.1.castSucc := by
  have hi : (index h a).val < 2 * g := by
    have h₁ := a.1.isLt
    have h₂ := a.2.isLt
    change 2 * a.1.val + a.2.val < 2 * g
    omega
  simp only [ownerQuery, dite_eq_left hi]
  apply Fin.ext
  change (2 * a.1.val + a.2.val) / 2 = a.1.val
  have h₂ := a.2.isLt
  omega

lemma ownerQuery_outside (i : Fin n) (hi : 2 * g ≤ i.val) : ownerQuery g i = Fin.last g := by
  simp only [ownerQuery, dite_eq_right (not_lt.mpr hi)]

end LongTails.Proofs.InterpolatedFiniteSumPairs
