import LongTails.Algorithms.GraceTree
import Mathlib.Tactic

namespace LongTails.Proofs.GraceTree

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceTree

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (T : Tree p S r)

lemma parent_iterate (i : Fin p.n) (hi : i ∈ T.nodes) (k : ℕ) :
    T.parent^[k] i ∈ T.nodes ∧ T.depth (T.parent^[k] i) = T.depth i - k := by
  induction k with
  | zero => exact ⟨hi, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨T.parent_mem _ ih.1, ?_⟩
    by_cases he : T.parent^[k] i = r
    · rw [he, T.parent_root, T.depth_root]
      have hf := ih.2
      rw [he, T.depth_root] at hf
      omega
    · have hf := T.parent_depth _ ih.1 he
      omega

lemma level_depth (i : Fin p.n) (hi : i ∈ T.nodes) (l : ℕ) :
    T.depth (T.atLevel l i) = min l (T.depth i) := by
  unfold Tree.atLevel
  rw [(parent_iterate T i hi _).2]
  omega

lemma depth_lt_workers (i : Fin p.n) (hi : i ∈ T.nodes) : T.depth i < p.n := by
  let node (l : Fin (T.depth i + 1)) := T.atLevel l.val i
  have levels (l : Fin (T.depth i + 1)) : T.depth (node l) = l.val :=
    (level_depth T i hi l.val).trans (min_eq_left (Nat.le_of_lt_succ l.isLt))
  have hinj : Function.Injective node := by
    intro l k h
    exact Fin.ext ((levels l).symm.trans ((congrArg T.depth h).trans (levels k)))
  have hc := Fintype.card_le_of_injective node hinj
  simpa using hc

lemma level_zero (i : Fin p.n) (hi : i ∈ T.nodes) : T.atLevel 0 i = r := by
  by_contra he
  have ha := T.parent_depth (T.atLevel 0 i) (parent_iterate T i hi _).1 he
  have hb := level_depth T i hi 0
  omega

lemma root_total (a : Fin p.n → ℕ) : T.subtotal a 0 r = ∑ i ∈ S, a i := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [level_zero T i (T.terminals hi)]

lemma level_step (i : Fin p.n) (l : ℕ) :
    T.atLevel l i = if T.depth i ≤ l then i else T.parent (T.atLevel (l + 1) i) := by
  by_cases h : T.depth i ≤ l
  · simp [h, Tree.atLevel, Nat.sub_eq_zero_of_le h]
  · simp only [h, ite_false, Tree.atLevel]
    rw [show T.depth i - l = (T.depth i - (l + 1)) + 1 by omega, Function.iterate_succ_apply']

lemma sum_children (a : Fin p.n → ℕ) (u : Fin p.n) (l : ℕ) (hu : T.depth u = l) :
    T.subtotal a l u = (if u ∈ S then a u else 0) +
      ∑ v ∈ T.children u, T.subtotal a (l + 1) v := by
  classical
  have hu' : (if u ∈ S then a u else 0) = ∑ i ∈ S, if i = u then a i else 0 := by simp
  rw [hu']
  unfold Tree.subtotal
  rw [Finset.sum_comm (s := T.children u), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hnodes := T.terminals hi
  have hmem := (parent_iterate T i hnodes (T.depth i - (l + 1))).1
  change T.atLevel (l + 1) i ∈ T.nodes at hmem
  have hs := level_depth T i hnodes (l + 1)
  simp only [Finset.sum_ite_eq, Finset.mem_filter, Tree.children]
  by_cases h : T.depth i ≤ l
  · have he : T.atLevel (l + 1) i = i := by
      simp [Tree.atLevel, Nat.sub_eq_zero_of_le (show T.depth i ≤ l + 1 by omega)]
    rw [level_step, ite_eq_left h, he]
    have hx : ¬ (i ∈ T.nodes ∧ i ≠ r ∧ T.parent i = u) := by
      rintro ⟨_, hne, eq⟩
      have hd := T.parent_depth i hnodes hne
      rw [eq, hu] at hd
      omega
    simp [hx]
  · have hx : T.atLevel (l + 1) i ≠ r := by
      intro he
      rw [he, T.depth_root] at hs
      omega
    have hiu : i ≠ u := by rintro rfl; omega
    simp [level_step T i l, h, hiu, hmem, hx]

end LongTails.Proofs.GraceTree
