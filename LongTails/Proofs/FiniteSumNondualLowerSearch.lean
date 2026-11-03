import Mathlib.Tactic

namespace LongTails.Proofs.FiniteSumNondualLowerSearch

noncomputable def searchMean (n : ℕ) : ℕ → (List Bool → Fin n) → Finset (Fin n) → ℝ
  | 0, _, _ => 0
  | T + 1, q, s =>
    if s.Nonempty then
      if q [] ∈ s then
        (1 + searchMean n T (fun h => q (true :: h)) Finset.univ +
          ((s.card : ℝ) - 1) * searchMean n T (fun h => q (false :: h)) (s.erase (q []))) /
          (s.card : ℝ)
      else searchMean n T (fun h => q (false :: h)) s
    else 0

def words (n : ℕ) : ℕ → Finset (List (Fin n))
  | 0 => {[]}
  | k + 1 => (Finset.univ ×ˢ words n k).image (fun p => p.1 :: p.2)

def discoveries (n : ℕ) : ℕ → (List Bool → Fin n) → List (Fin n) → ℕ
  | 0, _, _ => 0
  | _ + 1, _, [] => 0
  | T + 1, q, a :: w => if q [] = a then
      1 + discoveries n T (fun h => q (true :: h)) w
    else discoveries n T (fun h => q (false :: h)) (a :: w)

lemma words_sum (n k : ℕ) (f : List (Fin n) → ℝ) :
    (∑ w ∈ words n (k + 1), f w) = ∑ a : Fin n, ∑ w ∈ words n k, f (a :: w) := by
  rw [words, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x _ y _ h
    exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

lemma words_card (n k : ℕ) : (words n k).card = n ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    rw [words, Finset.card_image_of_injective]
    · simp [Finset.card_product, ih, pow_succ, mul_comm]
    · intro x y h
      exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

lemma discoveries_le_length (n T : ℕ) (q : List Bool → Fin n) (w : List (Fin n)) :
    discoveries n T q w ≤ w.length := by
  induction T generalizing q w with
  | zero => simp [discoveries]
  | succ T ih =>
    cases w with
    | nil => simp [discoveries]
    | cons a w =>
      simp only [discoveries]
      split
      · have h := ih (fun h => q (true :: h)) w
        simp only [List.length_cons]
        omega
      · exact ih _ _

lemma searchMean_nonneg (n T : ℕ) (q : List Bool → Fin n) (s : Finset (Fin n)) :
    0 ≤ searchMean n T q s := by
  induction T generalizing q s with
  | zero => simp [searchMean]
  | succ T ih =>
    rw [searchMean]
    split_ifs with hs hq
    · have hr : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
      apply div_nonneg
      · have h₁ := ih (fun h => q (true :: h)) Finset.univ
        have h₂ := ih (fun h => q (false :: h)) (s.erase (q []))
        nlinarith
      · positivity
    · exact ih _ _
    · rfl

lemma searchMean_empty (n T : ℕ) (q : List Bool → Fin n) :
    searchMean n T q ∅ = 0 := by
  cases T <;> simp [searchMean]

lemma searchMean_bound (n T : ℕ) (q : List Bool → Fin n) (s : Finset (Fin n)) :
    (n : ℝ) * searchMean n T q s ≤ 2 * T + ((n : ℝ) - s.card) := by
  induction T generalizing q s with
  | zero =>
    have hc : s.card ≤ n := by simpa using (Finset.card_le_univ s)
    have hcR : (s.card : ℝ) ≤ n := by exact_mod_cast hc
    simp only [searchMean, mul_zero, Nat.cast_zero, zero_add]
    linarith
  | succ T ih =>
    have hc : s.card ≤ n := by simpa using (Finset.card_le_univ s)
    have hcardR : (s.card : ℝ) ≤ n := by exact_mod_cast hc
    by_cases hs : s.Nonempty
    · have hr : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      by_cases hq : q [] ∈ s
      · rw [searchMean, ite_eq_left hs, ite_eq_left hq]
        have hi₁ := ih (fun h => q (true :: h)) Finset.univ
        simp only [Finset.card_univ, Fintype.card_fin, sub_self, add_zero] at hi₁
        have hi₂ := ih (fun h => q (false :: h)) (s.erase (q []))
        have hc : ((s.erase (q [])).card : ℝ) = (s.card : ℝ) - 1 := by
          have he := Finset.card_erase_add_one hq
          have heR : ((s.erase (q [])).card : ℝ) + 1 = s.card := by exact_mod_cast he
          linarith
        rw [hc] at hi₂
        rw [← mul_div_assoc, div_le_iff₀ hr]
        have hr₁ : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
        have hi₂' := mul_le_mul_of_nonneg_left hi₂ (by linarith : 0 ≤ (s.card : ℝ) - 1)
        simp only [Nat.cast_succ]
        nlinarith
      · rw [searchMean, ite_eq_left hs, ite_eq_right hq]
        have hi := ih (fun h => q (false :: h)) s
        simp only [Nat.cast_succ]
        linarith
    · rw [searchMean, ite_eq_right hs]
      simp only [mul_zero, Nat.cast_succ]
      have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
      linarith

lemma discovery_sum_bounds (n T : ℕ) :
    (∀ k q, (∑ w ∈ words n k, (discoveries n T q w : ℝ)) ≤
      (n : ℝ) ^ k * searchMean n T q Finset.univ) ∧
    (∀ k q s, (∑ a ∈ s, ∑ w ∈ words n k, (discoveries n T q (a :: w) : ℝ)) ≤
      (s.card : ℝ) * (n : ℝ) ^ k * searchMean n T q s) := by
  induction T with
  | zero => simp [discoveries, searchMean]
  | succ T ih =>
    have hhead : ∀ k q s,
        (∑ a ∈ s, ∑ w ∈ words n k, (discoveries n (T + 1) q (a :: w) : ℝ)) ≤
          (s.card : ℝ) * (n : ℝ) ^ k * searchMean n (T + 1) q s := by
      intro k q s
      by_cases hs : s.Nonempty
      · by_cases hq : q [] ∈ s
        · have hcard : ((s.erase (q [])).card : ℝ) = (s.card : ℝ) - 1 := by
            have h := Finset.card_erase_add_one hq
            have hr : ((s.erase (q [])).card : ℝ) + 1 = s.card := by exact_mod_cast h
            linarith
          have hr : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
          have hsplit : (∑ a ∈ s, ∑ w ∈ words n k,
              (discoveries n (T + 1) q (a :: w) : ℝ)) =
              ((n : ℝ) ^ k + ∑ w ∈ words n k,
                (discoveries n T (fun h => q (true :: h)) w : ℝ)) +
              ∑ a ∈ s.erase (q []), ∑ w ∈ words n k,
                (discoveries n T (fun h => q (false :: h)) (a :: w) : ℝ) := by
            rw [← Finset.add_sum_erase _ _ hq]
            congr 1
            · simp [discoveries, Finset.sum_add_distrib, words_card]
            · apply Finset.sum_congr rfl
              intro a ha
              have hne : q [] ≠ a := (Finset.mem_erase.mp ha).1.symm
              simp [discoveries, hne]
          rw [hsplit, searchMean, ite_eq_left hs, ite_eq_left hq]
          have hf := ih.1 k (fun h => q (true :: h))
          have hm := ih.2 k (fun h => q (false :: h)) (s.erase (q []))
          rw [hcard] at hm
          calc
            _ ≤ ((n : ℝ) ^ k + (n : ℝ) ^ k * searchMean n T
                (fun h => q (true :: h)) Finset.univ) +
                ((s.card : ℝ) - 1) * (n : ℝ) ^ k * searchMean n T
                (fun h => q (false :: h)) (s.erase (q [])) := by linarith
            _ = _ := by field_simp
        · have he : (∑ a ∈ s, ∑ w ∈ words n k,
              (discoveries n (T + 1) q (a :: w) : ℝ)) =
              ∑ a ∈ s, ∑ w ∈ words n k,
                (discoveries n T (fun h => q (false :: h)) (a :: w) : ℝ) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hne : q [] ≠ a := by intro h; exact hq (h.symm ▸ ha)
            simp [discoveries, hne]
          rw [he, searchMean, ite_eq_left hs, ite_eq_right hq]
          exact ih.2 k _ s
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simp [he, searchMean]
    refine ⟨?_, hhead⟩
    intro k q
    cases k with
    | zero => simpa [words, discoveries] using searchMean_nonneg n (T + 1) q Finset.univ
    | succ k =>
      rw [words_sum]
      simpa only [Finset.card_univ, Fintype.card_fin, pow_succ, mul_assoc, mul_comm,
        mul_left_comm] using hhead k q Finset.univ

lemma discovery_total_bound (n T k : ℕ) (q : List Bool → Fin n) :
    (n : ℝ) * (∑ w ∈ words n k, (discoveries n T q w : ℝ)) ≤
      2 * T * (n : ℝ) ^ k := by
  have hd := (discovery_sum_bounds n T).1 k q
  have hm := searchMean_bound n T q Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin, sub_self, add_zero] at hm
  calc
    _ ≤ (n : ℝ) * ((n : ℝ) ^ k * searchMean n T q Finset.univ) :=
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
    _ = (n : ℝ) ^ k * ((n : ℝ) * searchMean n T q Finset.univ) := by ring
    _ ≤ (n : ℝ) ^ k * (2 * T) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

lemma completion_count_bound (n T k : ℕ) (q : List Bool → Fin n) :
    (n : ℝ) * k * ((words n k).filter (fun w => k ≤ discoveries n T q w)).card ≤
      2 * T * (n : ℝ) ^ k := by
  let c := (words n k).filter (fun w => k ≤ discoveries n T q w)
  have hc : (k : ℝ) * c.card ≤ ∑ w ∈ words n k, (discoveries n T q w : ℝ) := by
    calc
      _ = ∑ _ ∈ c, (k : ℝ) := by simp [mul_comm]
      _ ≤ ∑ w ∈ c, (discoveries n T q w : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        exact_mod_cast (Finset.mem_filter.mp hw).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun w _ _ => Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm' : (n : ℝ) * k * c.card ≤
      (n : ℝ) * (∑ w ∈ words n k, (discoveries n T q w : ℝ)) := by
    simpa only [mul_assoc] using hm
  exact hm'.trans (discovery_total_bound n T k q)

lemma completion_fraction (n T k : ℕ) (q : List Bool → Fin n)
    (hn : 0 < n) (hk : 0 < k) (hT : 8 * T ≤ n * k) :
    4 * (((words n k).filter (fun w => k ≤ discoveries n T q w)).card : ℝ) ≤
      (n : ℝ) ^ k := by
  have hc := completion_count_bound n T k q
  have ht : 8 * (T : ℝ) ≤ (n : ℝ) * k := by exact_mod_cast hT
  have hp : (0 : ℝ) < (n : ℝ) * k := by positivity
  have hm := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ (n : ℝ) ^ k)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

lemma mem_words (n k : ℕ) (w : List (Fin n)) : w ∈ words n k ↔ w.length = k := by
  induction k generalizing w with
  | zero => cases w <;> simp [words]
  | succ k ih => cases w <;> simp [words, Finset.mem_image, Prod.exists, ih]

end LongTails.Proofs.FiniteSumNondualLowerSearch
