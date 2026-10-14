import LongTails.Proofs.ReshufflingExpansion
import LongTails.Proofs.ReshufflingCollisions

open scoped BigOperators

namespace OracleTemplate.Reshuffling

lemma finset_sum_list_sum {J I V : Type*} [AddCommMonoid V]
    (s : Finset J) (w : List I) (F : J → I → V) :
    (∑ j ∈ s, (w.map (F j)).sum) = (w.map (fun i => ∑ j ∈ s, F j i)).sum := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

lemma nodup_family_average {I : Type*} [Fintype I] [DecidableEq I]
    (F : List I → ℝ) (family : List (List I)) (m : ℕ)
    (hw : ∀ w ∈ family, w.Nodup ∧ w.length = m) :
    (Fintype.card (Fin m ↪ I) : ℝ) *
        (family.map (fun w => ∑ π : Equiv.Perm I, F (w.map π))).sum =
      (Fintype.card (Equiv.Perm I) : ℝ) * family.length *
        ∑ g : Fin m ↪ I, F (List.ofFn g) := by
  induction family with
  | nil => simp
  | cons w family ih =>
    have hw0 := hw w (by simp)
    have hrest := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
    have hhead := nodup_word_average F w m hw0.1 hw0.2
    simp only [nsmul_eq_mul] at hhead
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [mul_add, hhead, hrest]
    ring

lemma palindrome_distinct_average {n : ℕ} (F : List (Fin n) → ℝ)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (m : ℕ) (hm : m ≤ n) :
    (∑ π : Equiv.Perm (Fin n),
      ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide v.Nodup)).map
        (fun v => F (v.map π))).sum) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 2 ^ m / m.factorial *
        ∑ g : Fin m ↪ Fin n, F (List.ofFn g) := by
  classical
  let family := ((w ++ w.reverse).sublistsLen m).filter (fun v => decide v.Nodup)
  have hwords : ∀ v ∈ family, v.Nodup ∧ v.length = m := by
    intro v hv
    obtain ⟨hv, hn⟩ := List.mem_filter.mp hv
    exact ⟨of_decide_eq_true hn, List.length_of_sublistsLen hv⟩
  have hc : family.length = 2 ^ m * n.choose m := by
    rw [← distinctSubwordCount_eq_length, palindrome_distinct_count _ hw, hlen]
  have ha := nodup_family_average F family m hwords
  rw [embedding_card_factorial_choose, hc] at ha
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at ha
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hp : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  rw [finset_sum_list_sum]
  change (family.map (fun v => ∑ π : Equiv.Perm (Fin n), F (v.map π))).sum = _
  apply (mul_left_cancel₀ (mul_ne_zero hf hp))
  calc
    _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (2 ^ m * (n.choose m : ℝ)) *
        ∑ g : Fin m ↪ Fin n, F (List.ofFn g) := ha
    _ = _ := by field_simp

lemma palindrome_distinct_average_all {n : ℕ} (F : List (Fin n) → ℝ)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (m : ℕ) :
    (∑ π : Equiv.Perm (Fin n),
      ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide v.Nodup)).map
        (fun v => F (v.map π))).sum) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 2 ^ m / m.factorial *
        ∑ g : Fin m ↪ Fin n, F (List.ofFn g) := by
  classical
  by_cases hm : m ≤ n
  · exact palindrome_distinct_average F w hw hlen m hm
  · let : IsEmpty (Fin m ↪ Fin n) := ⟨fun f => hm (by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective)⟩
    have he : (((w ++ w.reverse).sublistsLen m).filter (fun v => decide v.Nodup)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro v hv
      have hn : ¬v.Nodup := by
        intro hnd
        apply hm
        simpa only [List.length_of_sublistsLen hv, Fintype.card_fin] using hnd.length_le_card
      simpa only [decide_eq_true_eq] using hn
    simp [he]

lemma list_sum_filter_partition {I V : Type*} [AddCommMonoid V]
    (w : List I) (p : I → Bool) (F : I → V) :
    (w.map F).sum = ((w.filter p).map F).sum +
      ((w.filter (fun i => !p i)).map F).sum := by
  induction w with
  | nil => simp
  | cons i w ih => cases h : p i <;> simp [h, ih, add_assoc, add_left_comm]

lemma palindrome_coefficient_identity {n : ℕ} (F : List (Fin n) → ℝ)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (m : ℕ) :
    (∑ π : Equiv.Perm (Fin n),
      ((w ++ w.reverse).sublistsLen m |>.map (fun v => F (v.map π))).sum) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 2 ^ m / m.factorial *
        ((∑ f : Fin m → Fin n, F (List.ofFn f)) -
          ∑ f ∈ Finset.univ.filter (fun f : Fin m → Fin n => ¬Function.Injective f), F (List.ofFn f)) +
      ∑ π : Equiv.Perm (Fin n),
        ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide (¬v.Nodup))).map
          (fun v => F (v.map π))).sum := by
  classical
  have hpart := word_sum_partition m (fun f : Fin m → Fin n => F (List.ofFn f))
  have he : ∀ π : Equiv.Perm (Fin n),
      (((w ++ w.reverse).sublistsLen m).map (fun v => F (v.map π))).sum =
      ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide v.Nodup)).map
        (fun v => F (v.map π))).sum +
      ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide (¬v.Nodup))).map
        (fun v => F (v.map π))).sum := by
    intro π
    simpa using list_sum_filter_partition ((w ++ w.reverse).sublistsLen m)
      (fun v => decide v.Nodup) (fun v => F (v.map π))
  simp_rw [he]
  rw [Finset.sum_add_distrib, palindrome_distinct_average_all F w hw hlen m, hpart]
  ring

end OracleTemplate.Reshuffling
