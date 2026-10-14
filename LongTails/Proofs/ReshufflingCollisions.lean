import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.Reshuffling

lemma paired_word_card_le {m n : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) :
    Fintype.card {f : Fin (m + 1) → Fin n // f i = f j} ≤ n ^ m := by
  classical
  let erase : {f : Fin (m + 1) → Fin n // f i = f j} → (Fin m → Fin n) :=
    fun f k => f.val (j.succAbove k)
  have he : Function.Injective erase := by
    intro f g hfg
    apply Subtype.ext
    funext k
    by_cases hk : k = j
    · subst k
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hij
      have heq := congrFun hfg a
      change f.val (j.succAbove a) = g.val (j.succAbove a) at heq
      rw [ha, f.property, g.property] at heq
      exact heq
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hk
      exact congrFun hfg a
  simpa using Fintype.card_le_of_injective erase he

lemma collision_word_card_le (m n : ℕ) :
    (Finset.univ.filter (fun f : Fin (m + 1) → Fin n => ¬ Function.Injective f)).card ≤
      (m + 1) * m * n ^ m := by
  classical
  let pairs := (Finset.univ : Finset (Fin (m + 1))).offDiag
  let events := fun p : Fin (m + 1) × Fin (m + 1) =>
    Finset.univ.filter (fun f : Fin (m + 1) → Fin n => f p.1 = f p.2)
  have he : Finset.univ.filter (fun f : Fin (m + 1) → Fin n => ¬ Function.Injective f) =
      pairs.biUnion events := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      pairs, Finset.mem_offDiag, events]
    constructor
    · intro hf
      obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hf
      exact ⟨(i, j), hne, heq⟩
    · rintro ⟨⟨i, j⟩, hne, hf⟩ hinj
      exact hne (hinj hf)
  rw [he]
  calc
    _ ≤ ∑ p ∈ pairs, (events p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, n ^ m := by
      apply Finset.sum_le_sum
      intro p hp
      have hne := (Finset.mem_offDiag.mp hp).2.2
      simpa only [events, Fintype.card_subtype] using paired_word_card_le p.1 p.2 hne
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, pairs, Finset.offDiag_card,
        Finset.card_univ, Fintype.card_fin]
      rw [show (m + 1) * (m + 1) - (m + 1) = (m + 1) * m by
        rw [Nat.mul_succ, Nat.add_sub_cancel]]
      simp

def distinctSubwordCount {I : Type*} [DecidableEq I] (w : List I) (m : ℕ) : ℕ :=
  w.sublists.countP (fun v => decide (v.Nodup ∧ v.length = m))

lemma sublistsLen_eq_filter {I : Type*} (w : List I) (m : ℕ) :
    w.sublistsLen m = w.sublists'.filter (fun v => decide (v.length = m)) := by
  induction w generalizing m with
  | nil => cases m <;> simp
  | cons a w ih =>
    cases m with
    | zero =>
      simp only [List.sublistsLen_zero, List.sublists'_cons, List.filter_append,
        List.filter_map, Function.comp_def, List.length_cons, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, decide_false, List.filter_false, List.map_nil, List.append_nil]
      simpa only [List.sublistsLen_zero] using ih 0
    | succ m =>
      simp only [List.sublistsLen_succ_cons, List.sublists'_cons, List.filter_append,
        List.filter_map, Function.comp_def, List.length_cons, Nat.add_right_cancel_iff, ih]

lemma distinctSubwordCount_eq_length {I : Type*} [DecidableEq I] (w : List I) (m : ℕ) :
    distinctSubwordCount w m =
      ((w.sublistsLen m).filter (fun v => decide v.Nodup)).length := by
  unfold distinctSubwordCount
  rw [(List.sublists_perm_sublists' w).countP_eq, List.countP_eq_length_filter,
    sublistsLen_eq_filter, List.filter_filter]
  congr 2

lemma distinctSubwordCount_zero {I : Type*} [DecidableEq I] (w : List I) :
    distinctSubwordCount w 0 = 1 := by
  induction w with
  | nil => simp [distinctSubwordCount]
  | cons a w ih =>
    unfold distinctSubwordCount at *
    rw [(List.sublists_cons_perm_append a w).countP_eq]
    simp only [List.countP_append, List.countP_map, Function.comp_def]
    have hz : w.sublists.countP (fun v => decide ((a :: v).Nodup ∧ (a :: v).length = 0)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro v hv
      simp
    rw [hz, Nat.add_zero, ih]

lemma distinctSubwordCount_wrap {I : Type*} [DecidableEq I] (a : I) (w : List I)
    (ha : a ∉ w) (m : ℕ) :
    distinctSubwordCount (a :: (w ++ [a])) (m + 1) =
      distinctSubwordCount w (m + 1) + 2 * distinctSubwordCount w m := by
  have hfresh : ∀ v ∈ w.sublists, a ∉ v := by
    intro v hv hav
    exact ha ((List.mem_sublists.mp hv).subset hav)
  unfold distinctSubwordCount
  rw [(List.sublists_cons_perm_append a (w ++ [a])).countP_eq]
  simp only [List.sublists_concat, List.map_append, List.countP_append,
    List.countP_map, Function.comp_def]
  have hr : w.sublists.countP (fun v => decide ((v ++ [a]).Nodup ∧ (v ++ [a]).length = m + 1)) =
      w.sublists.countP (fun v => decide (v.Nodup ∧ v.length = m)) := by
    apply List.countP_congr
    intro v hv
    simp [List.nodup_append]
    intro hlen hnd b hb hba
    exact hfresh v hv (hba ▸ hb)
  have hl : w.sublists.countP (fun v => decide ((a :: v).Nodup ∧ (a :: v).length = m + 1)) =
      w.sublists.countP (fun v => decide (v.Nodup ∧ v.length = m)) := by
    apply List.countP_congr
    intro v hv
    simp [List.nodup_cons, hfresh v hv]
  have hb : w.sublists.countP (fun v => decide ((a :: (v ++ [a])).Nodup ∧
      (a :: (v ++ [a])).length = m + 1)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro v hv
    simp [List.nodup_cons]
  rw [hr, hl, hb]
  omega

lemma palindrome_distinct_count {I : Type*} [DecidableEq I] (w : List I) (hw : w.Nodup)
    (m : ℕ) : distinctSubwordCount (w ++ w.reverse) m = 2 ^ m * w.length.choose m := by
  induction w generalizing m with
  | nil => cases m <;> simp [distinctSubwordCount]
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := List.nodup_cons.mp hw
    cases m with
    | zero => simp [distinctSubwordCount_zero]
    | succ m =>
      rw [List.reverse_cons, List.cons_append, ← List.append_assoc,
        distinctSubwordCount_wrap a (w ++ w.reverse) (by simpa using ha),
        ih hw, ih hw, List.length_cons, Nat.choose_succ_succ, pow_succ]
      ring

lemma injective_word_card (m n : ℕ) :
    (Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f)).card = n.descFactorial m := by
  classical
  let e : {f : Fin m → Fin n // Function.Injective f} ≃ (Fin m ↪ Fin n) :=
    { toFun := fun f => ⟨f.val, f.property⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_subtype, Fintype.card_embedding_eq, Fintype.card_fin] using hc

lemma free_collision_mass (m n : ℕ) :
    (n : ℝ) ^ (m + 2) - n.descFactorial (m + 2) ≤
      ((m + 2) * (m + 1) : ℝ) * (n : ℝ) ^ (m + 1) := by
  classical
  have ht := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (m + 2) → Fin n))) (p := Function.Injective)
  rw [injective_word_card] at ht
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at ht
  have hc := collision_word_card_le (m + 1) n
  have hr : (n.descFactorial (m + 2) : ℝ) +
      ((Finset.univ.filter (fun f : Fin (m + 2) → Fin n => ¬ Function.Injective f)).card : ℝ) =
      (n : ℝ) ^ (m + 2) := by exact_mod_cast ht
  have hb : ((Finset.univ.filter (fun f : Fin (m + 2) → Fin n => ¬ Function.Injective f)).card : ℝ) ≤
      ((m + 2) * (m + 1) : ℝ) * (n : ℝ) ^ (m + 1) := by exact_mod_cast hc
  linarith

lemma palindrome_collision_mass (m n : ℕ) :
    ((2 * n).choose (m + 2) : ℝ) - 2 ^ (m + 2) * (n.choose (m + 2) : ℝ) ≤
      2 ^ (m + 2) / (m + 2).factorial *
        ((n : ℝ) ^ (m + 2) - n.descFactorial (m + 2)) := by
  have hc : ((2 * n).choose (m + 2) : ℝ) ≤
      (2 * (n : ℝ)) ^ (m + 2) / (m + 2).factorial := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.choose_le_pow_div (α := ℝ) (m + 2) (2 * n))
  have hf : (n.descFactorial (m + 2) : ℝ) =
      ((m + 2).factorial : ℝ) * (n.choose (m + 2) : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n (m + 2)
  have hp : ((m + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (m + 2))
  rw [hf]
  calc
    _ ≤ (2 * (n : ℝ)) ^ (m + 2) / (m + 2).factorial -
        2 ^ (m + 2) * (n.choose (m + 2) : ℝ) := sub_le_sub_right hc _
    _ = _ := by rw [mul_pow]; field_simp

lemma scaled_free_collision_le (m n : ℕ) :
    2 ^ (m + 2) / ((m + 2).factorial : ℝ) *
        ((n : ℝ) ^ (m + 2) - n.descFactorial (m + 2)) ≤
      2 * (2 * (n : ℝ)) ^ (m + 1) := by
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  calc
    _ ≤ 2 ^ (m + 2) / ((m + 2).factorial : ℝ) *
        (((m + 2) * (m + 1) : ℝ) * (n : ℝ) ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left (free_collision_mass m n) (by positivity)
    _ = 2 * (2 * (n : ℝ)) ^ (m + 1) / m.factorial := by
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_pow, pow_succ]
      field_simp
      ring
    _ ≤ _ := div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m))

lemma palindrome_collision_le (m n : ℕ) :
    ((2 * n).choose (m + 2) : ℝ) - 2 ^ (m + 2) * (n.choose (m + 2) : ℝ) ≤
      2 * (2 * (n : ℝ)) ^ (m + 1) :=
  (palindrome_collision_mass m n).trans (scaled_free_collision_le m n)

lemma palindrome_repeated_count {I : Type*} [DecidableEq I] (w : List I)
    (hw : w.Nodup) (m : ℕ) :
    ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide (¬ v.Nodup))).length : ℝ) =
      ((2 * w.length).choose m : ℝ) - 2 ^ m * (w.length.choose m : ℝ) := by
  have ht := List.length_eq_countP_add_countP (fun v : List I => decide v.Nodup)
    (l := (w ++ w.reverse).sublistsLen m)
  simp only [List.countP_eq_length_filter, decide_eq_true_eq] at ht
  rw [← distinctSubwordCount_eq_length, palindrome_distinct_count _ hw,
    List.length_sublistsLen, List.length_append, List.length_reverse] at ht
  have hreal : ((2 * w.length).choose m : ℝ) =
      2 ^ m * (w.length.choose m : ℝ) +
        ((((w ++ w.reverse).sublistsLen m).filter (fun v => decide (¬ v.Nodup))).length : ℝ) := by
    exact_mod_cast (show (2 * w.length).choose m = _ by simpa only [two_mul] using ht)
  linarith

lemma palindrome_repeated_two_count {I : Type*} [DecidableEq I]
    (w : List I) (hw : w.Nodup) :
    ((((w ++ w.reverse).sublistsLen 2).filter (fun v => decide (¬ v.Nodup))).length : ℝ) =
      w.length := by
  rw [palindrome_repeated_count w hw, Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

end OracleTemplate.Reshuffling
