import LongTails.Algorithms.UniversalSilver
import LongTails.Proofs.SilverCertificate
import Mathlib.Data.List.GetD

namespace LongTails.Proofs.UniversalSilverSchedule

open LongTails.Algorithms.SilverSchedule LongTails.Algorithms.UniversalSilver
open LongTails.Proofs.SilverCertificate

lemma ruler_split (a : ℕ) : ruler a = (ruler a).dropLast ++ [a + 1] := by
  cases a with
  | zero => rfl
  | succ a =>
    simp only [ruler, List.dropLast_concat]

lemma ruler_length (a : ℕ) : (ruler a).length = 2 ^ a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hs := congrArg List.length (ruler_split a)
    simp only [List.length_append, List.length_singleton] at hs
    simp only [ruler, List.length_append, List.length_singleton, pow_succ]
    omega

lemma ruler_pos (a : ℕ) : ∀ o ∈ ruler a, 1 ≤ o := by
  induction a with
  | zero => simp [ruler]
  | succ a ih =>
    intro o ho
    simp only [ruler, List.mem_append, List.mem_singleton] at ho
    rcases ho with (ho | ho) | rfl
    · exact ih o ho
    · exact ih o (List.mem_of_mem_dropLast ho)
    · omega

lemma ruler_power_sum (a : ℕ) : ((ruler a).map (fun o => 2 ^ o)).sum = (a + 2) * 2 ^ a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hs := congrArg (fun l => (l.map (fun o => 2 ^ o)).sum) (ruler_split a)
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hs
    simp only [ruler, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, pow_succ]
    rw [ih] at hs ⊢
    rw [pow_succ] at hs
    zify at hs ⊢
    linear_combination -hs

lemma blocks_length (a : ℕ) : (blocks a).length = (a + 1) * 2 ^ a := by
  have hb : ∀ l : List ℕ, (∀ o ∈ l, 1 ≤ o) →
      (l.flatMap steps).length + l.length = (l.map (fun o => 2 ^ o)).sum := by
    intro l hl
    induction l with
    | nil => rfl
    | cons o l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.map_cons,
        List.sum_cons]
      have h1 := steps_length o
      have h2 := ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho'))
      omega
  have h := hb (ruler a) (ruler_pos a)
  rw [ruler_length, ruler_power_sum] at h
  unfold blocks
  nlinarith [h]

lemma ruler_count (m a : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ a + 1) :
    2 ^ (a + 1 - m) ≤ (ruler a).countP (fun o => decide (m ≤ o)) := by
  induction a with
  | zero =>
    have hm' : m = 1 := by omega
    subst hm'
    simp [ruler]
  | succ a ih =>
    have hs := congrArg (fun l => l.countP (fun o => decide (m ≤ o))) (ruler_split a)
    simp only [List.countP_append, List.countP_cons, List.countP_nil] at hs
    simp only [ruler, List.countP_append, List.countP_cons, List.countP_nil]
    by_cases ha : m ≤ a + 1
    · have h := ih ha
      have hm2 : m ≤ a + 2 := by omega
      simp only [ha, hm2, decide_true, ite_true] at hs ⊢
      have he : a + 1 + 1 - m = (a + 1 - m) + 1 := by omega
      rw [he, pow_succ]
      omega
    · have hm' : m = a + 2 := by omega
      subst hm'
      simp

lemma ruler_prefix {a b : ℕ} (h : a ≤ b) : ruler a <+: ruler b := by
  induction h with
  | refl => exact List.prefix_refl _
  | @step n _ ih =>
    have hs : ruler n <+: ruler (n + 1) := by
      simp only [ruler]
      exact (List.prefix_append _ _).trans (List.prefix_append _ _)
    exact ih.trans hs

lemma blocks_prefix {a b : ℕ} (h : a ≤ b) : blocks a <+: blocks b := by
  obtain ⟨t, ht⟩ := ruler_prefix h
  refine ⟨t.flatMap steps, ?_⟩
  unfold blocks
  rw [← ht, List.flatMap_append]

lemma blocks_positive (a : ℕ) : ∀ h ∈ blocks a, 0 < h := by
  intro h hh
  unfold blocks at hh
  obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp hh
  exact steps_positive o h ho

lemma lt_blocks_length (t : ℕ) : t < (blocks t).length := by
  rw [blocks_length]
  have : t < 2 ^ t := Nat.lt_two_pow_self
  nlinarith

lemma stepsize_eq (a t : ℕ) (ht : t < (blocks a).length) :
    stepsize t = (blocks a)[t] := by
  unfold stepsize
  rcases le_total t a with h | h
  · obtain ⟨u, hu⟩ := blocks_prefix h
    have hl := lt_blocks_length t
    rw [List.getD_eq_getElem _ _ hl]
    simp only [← hu, List.getElem_append_left hl]
  · obtain ⟨u, hu⟩ := blocks_prefix h
    have hl := lt_blocks_length t
    rw [List.getD_eq_getElem _ _ hl]
    simp only [← hu, List.getElem_append_left ht]

lemma stepsize_positive (t : ℕ) : 0 < stepsize t := by
  rw [stepsize_eq t t (lt_blocks_length t)]
  exact blocks_positive t _ (List.getElem_mem _)

end LongTails.Proofs.UniversalSilverSchedule
