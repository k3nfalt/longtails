import LongTails.Proofs.FiniteSumNondualLowerSearch

open scoped BigOperators
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumDistinctSearch

open FiniteSumNondualLowerSearch (discoveries)

noncomputable def words {n : ℕ} (U : Finset (Fin n)) : ℕ → Finset (List (Fin n))
  | 0 => {[]}
  | k + 1 => U.biUnion (fun a => (words (U.erase a) k).image (List.cons a))

lemma words_sum {n : ℕ} (U : Finset (Fin n)) (k : ℕ) (f : List (Fin n) → ℝ) :
    (∑ w ∈ words U (k + 1), f w) = ∑ a ∈ U, ∑ w ∈ words (U.erase a) k, f (a :: w) := by
  rw [words, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro w hw₁ hw₂
    rcases Finset.mem_image.mp hw₁ with ⟨u, _, hu⟩
    rcases Finset.mem_image.mp hw₂ with ⟨v, _, hv⟩
    exact hab (List.cons.inj (hu.trans hv.symm)).1

lemma words_card {n : ℕ} (U : Finset (Fin n)) (k : ℕ) :
    (words U k).card = U.card.descFactorial k := by
  induction k generalizing U with
  | zero => simp [words]
  | succ k ih =>
    have hh := words_sum U k (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    have hc : ∀ a ∈ U, (words (U.erase a) k).card = (U.card - 1).descFactorial k := by
      intro a ha
      rw [ih, Finset.card_erase_of_mem ha]
    simp_rw [Finset.sum_congr rfl (fun a ha => congrArg (fun z : ℕ => (z : ℝ)) (hc a ha))] at hh
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    have he : U.card.descFactorial (k + 1) = U.card * (U.card - 1).descFactorial k := by
      cases h : U.card with
      | zero => simp
      | succ u => simpa using Nat.succ_descFactorial_succ u k
    rw [he]
    exact_mod_cast hh

noncomputable def mean (n : ℕ) : ℕ → ℕ → (List Bool → Fin n) → Finset (Fin n) → Finset (Fin n) → ℝ
  | 0, _, _, _, _ => 0
  | _ + 1, 0, _, _, _ => 0
  | b + 1, k + 1, q, U, S =>
    if S.Nonempty then
      if q [] ∈ S then
        (1 + mean n b k (fun h => q (true :: h)) (U.erase (q [])) (U.erase (q [])) +
          ((S.card : ℝ) - 1) * mean n b (k + 1) (fun h => q (false :: h)) U (S.erase (q []))) /
          (S.card : ℝ)
      else mean n b (k + 1) (fun h => q (false :: h)) U S
    else 0

lemma mean_bound (n b : ℕ) : ∀ (k : ℕ) (q : List Bool → Fin n) (U S : Finset (Fin n)) (K : ℝ),
    S ⊆ U → K + k ≤ U.card + 1 →
    K * mean n b k q U S ≤ 2 * b + (U.card - (S.card : ℝ)) := by
  induction b with
  | zero =>
    intro k q U S K hSU _
    have hc : (S.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hSU
    simp only [mean, mul_zero, Nat.cast_zero, mul_zero, zero_add]
    linarith
  | succ b ih =>
    intro k q U S K hSU hK
    have hc : (S.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hSU
    cases k with
    | zero =>
      simp only [mean, mul_zero]
      have hb : (0 : ℝ) ≤ b + 1 := by positivity
      linarith
    | succ k =>
      by_cases hs : S.Nonempty
      · have hspos : (0 : ℝ) < S.card := by exact_mod_cast hs.card_pos
        have hs1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hs.card_pos
        by_cases hq : q [] ∈ S
        · have hqU : q [] ∈ U := hSU hq
          have hU : ((U.erase (q [])).card : ℝ) = U.card - 1 := by
            have hh := Finset.card_erase_add_one hqU
            have hhR : ((U.erase (q [])).card : ℝ) + 1 = U.card := by exact_mod_cast hh
            linarith
          have hS : ((S.erase (q [])).card : ℝ) = S.card - 1 := by
            have hh := Finset.card_erase_add_one hq
            have hhR : ((S.erase (q [])).card : ℝ) + 1 = S.card := by exact_mod_cast hh
            linarith
          have ht := ih k (fun h => q (true :: h)) (U.erase (q [])) (U.erase (q [])) K
            (Finset.Subset.refl _) (by rw [hU]; simp only [Nat.cast_succ] at hK; linarith)
          have hf := ih (k + 1) (fun h => q (false :: h)) U (S.erase (q [])) K
            ((Finset.erase_subset _ _).trans hSU) hK
          simp only [sub_self, add_zero] at ht
          rw [hS] at hf
          have hfm := mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ (S.card : ℝ) - 1)
          rw [mean, ite_eq_left hs, ite_eq_left hq, ← mul_div_assoc, div_le_iff₀ hspos]
          simp only [Nat.cast_succ] at *
          have hk : (0 : ℝ) ≤ k := by positivity
          nlinarith only [ht, hfm, hK, hk]
        · rw [mean, ite_eq_left hs, ite_eq_right hq]
          have hh := ih (k + 1) (fun h => q (false :: h)) U S K hSU hK
          simp only [Nat.cast_succ]
          linarith
      · rw [mean, ite_eq_right hs, mul_zero]
        have hb : (0 : ℝ) ≤ b + 1 := by positivity
        linarith

lemma discovery_sum (n b : ℕ) :
    (∀ k (q : List Bool → Fin n) U,
      (∑ w ∈ words U k, (discoveries n b q w : ℝ)) =
        (words U k).card * mean n b k q U U) ∧
    (∀ k (q : List Bool → Fin n) U S, S ⊆ U →
      (∑ a ∈ S, ∑ w ∈ words (U.erase a) k, (discoveries n b q (a :: w) : ℝ)) =
        (S.card : ℝ) * ((U.card - 1).descFactorial k : ℝ) * mean n b (k + 1) q U S) := by
  induction b with
  | zero => simp [discoveries, mean]
  | succ b ih =>
    have hhead : ∀ k (q : List Bool → Fin n) U S, S ⊆ U →
        (∑ a ∈ S, ∑ w ∈ words (U.erase a) k, (discoveries n (b + 1) q (a :: w) : ℝ)) =
          (S.card : ℝ) * ((U.card - 1).descFactorial k : ℝ) * mean n (b + 1) (k + 1) q U S := by
      intro k q U S hSU
      by_cases hs : S.Nonempty
      · by_cases hq : q [] ∈ S
        · have hqU : q [] ∈ U := hSU hq
          have hcard : ((S.erase (q [])).card : ℝ) = S.card - 1 := by
            have hh := Finset.card_erase_add_one hq
            have hhR : ((S.erase (q [])).card : ℝ) + 1 = S.card := by exact_mod_cast hh
            linarith
          have hr : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
          have hsplit : (∑ a ∈ S, ∑ w ∈ words (U.erase a) k,
              (discoveries n (b + 1) q (a :: w) : ℝ)) =
              ((words (U.erase (q [])) k).card + ∑ w ∈ words (U.erase (q [])) k,
                (discoveries n b (fun h => q (true :: h)) w : ℝ)) +
              ∑ a ∈ S.erase (q []), ∑ w ∈ words (U.erase a) k,
                (discoveries n b (fun h => q (false :: h)) (a :: w) : ℝ) := by
            rw [← Finset.add_sum_erase _ _ hq]
            congr 1
            · simp [discoveries, Finset.sum_add_distrib]
            · apply Finset.sum_congr rfl
              intro a ha
              have hne : q [] ≠ a := (Finset.mem_erase.mp ha).1.symm
              simp [discoveries, hne]
          rw [hsplit, ih.1, ih.2 k _ U (S.erase (q [])) ((Finset.erase_subset _ _).trans hSU),
            words_card, Finset.card_erase_of_mem hqU, hcard,
            mean, ite_eq_left hs, ite_eq_left hq]
          field_simp
        · have he : (∑ a ∈ S, ∑ w ∈ words (U.erase a) k,
              (discoveries n (b + 1) q (a :: w) : ℝ)) =
              ∑ a ∈ S, ∑ w ∈ words (U.erase a) k,
                (discoveries n b (fun h => q (false :: h)) (a :: w) : ℝ) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hne : q [] ≠ a := by intro hh; exact hq (hh.symm ▸ ha)
            simp [discoveries, hne]
          rw [he, mean, ite_eq_left hs, ite_eq_right hq]
          exact ih.2 k _ U S hSU
      · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simp [he, mean]
    refine ⟨?_, hhead⟩
    intro k q U
    cases k with
    | zero => simp [words, discoveries, mean]
    | succ k =>
      rw [words_sum, hhead k q U U (Finset.Subset.refl _), words_card]
      have he : U.card.descFactorial (k + 1) = U.card * (U.card - 1).descFactorial k := by
        cases hh : U.card with
        | zero => simp
        | succ u => simpa using Nat.succ_descFactorial_succ u k
      rw [he, Nat.cast_mul]

lemma discovery_total_bound (n b k : ℕ) (q : List Bool → Fin n) (U : Finset (Fin n))
    (K : ℝ) (hK : K + k ≤ U.card + 1) :
    K * (∑ w ∈ words U k, (discoveries n b q w : ℝ)) ≤ 2 * b * (words U k).card := by
  rw [(discovery_sum n b).1]
  have hh := mean_bound n b k q U U K (Finset.Subset.refl _) hK
  simp only [sub_self, add_zero] at hh
  have hm := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (words U k).card : (0 : ℝ) ≤ _)
  nlinarith only [hm]

lemma mem_words {n : ℕ} (U : Finset (Fin n)) (k : ℕ) (w : List (Fin n)) :
    w ∈ words U k ↔ w.length = k ∧ w.Nodup ∧ ∀ a ∈ w, a ∈ U := by
  induction k generalizing U w with
  | zero => cases w <;> simp [words]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      have he : a :: w ∈ words U (k + 1) ↔ a ∈ U ∧ w ∈ words (U.erase a) k := by
        rw [words, Finset.mem_biUnion]
        constructor
        · rintro ⟨b, hb, hw⟩
          rcases Finset.mem_image.mp hw with ⟨v, hv, he⟩
          rcases List.cons.inj he with ⟨rfl, rfl⟩
          exact ⟨hb, hv⟩
        · rintro ⟨ha, hw⟩
          exact ⟨a, ha, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
      rw [he, ih]
      simp only [List.length_cons, Nat.succ.injEq, List.nodup_cons,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨ha, hlen, hnodup, hmem⟩
        refine ⟨hlen, ⟨?_, hnodup⟩, ha, ?_⟩
        · intro haw
          exact (Finset.mem_erase.mp (hmem a haw)).1 rfl
        · intro b hb
          exact (Finset.mem_erase.mp (hmem b hb)).2
      · rintro ⟨hlen, ⟨hanot, hnodup⟩, ha, hmem⟩
        refine ⟨ha, hlen, hnodup, ?_⟩
        intro b hb
        apply Finset.mem_erase.mpr
        refine ⟨?_, hmem b hb⟩
        intro hba
        exact hanot (hba ▸ hb)

lemma words_nonempty {n : ℕ} (U : Finset (Fin n)) (k : ℕ) (hk : k ≤ U.card) :
    (words U k).Nonempty := by
  apply Finset.card_pos.mp
  rw [words_card]
  exact Nat.descFactorial_pos.mpr hk

noncomputable def ownerPool (m : ℕ) : Finset (Fin (m + 1)) := Finset.univ.erase (Fin.last m)

lemma ownerPool_card (m : ℕ) : (ownerPool m).card = m := by simp [ownerPool]

abbrev OwnerWords (m T : ℕ) := ↥(words (ownerPool m) T)

lemma ownerWords_nonempty (m T : ℕ) (hT : T ≤ m) : Nonempty (OwnerWords m T) := by
  have hh := words_nonempty (ownerPool m) T (by simpa only [ownerPool_card] using hT)
  obtain ⟨w, hw⟩ := hh
  exact ⟨⟨w, hw⟩⟩

lemma ownerWord_length {m T : ℕ} (w : OwnerWords m T) : w.val.length = T :=
  ((mem_words (ownerPool m) T w.val).mp w.property).1

lemma ownerWord_nodup {m T : ℕ} (w : OwnerWords m T) : w.val.Nodup :=
  ((mem_words (ownerPool m) T w.val).mp w.property).2.1

lemma ownerWord_mem {m T : ℕ} (w : OwnerWords m T) (a : Fin (m + 1)) (ha : a ∈ w.val) : a.val < m := by
  have hh := ((mem_words (ownerPool m) T w.val).mp w.property).2.2 a ha
  have hne : a ≠ Fin.last m := (Finset.mem_erase.mp hh).1
  have hval := a.isLt
  have hnval : a.val ≠ m := by
    intro he
    apply hne
    exact Fin.ext he
  omega

noncomputable def owner {m T : ℕ} (w : OwnerWords m T) : Fin T ↪ Fin m where
  toFun j :=
    let i : Fin w.val.length := ⟨j.val, by rw [ownerWord_length w]; exact j.isLt⟩
    ⟨(w.val.get i).val, ownerWord_mem w _ (List.get_mem _ _)⟩
  inj' := by
    intro i j hij
    have hv := congrArg Fin.val hij
    have he : w.val.get ⟨i.val, by rw [ownerWord_length w]; exact i.isLt⟩ =
        w.val.get ⟨j.val, by rw [ownerWord_length w]; exact j.isLt⟩ := Fin.ext hv
    have hh := (ownerWord_nodup w).injective_get he
    exact Fin.ext (congrArg (fun z : Fin w.val.length => z.val) hh)

lemma owner_cast {m T : ℕ} (w : OwnerWords m T) (j : Fin T) :
    (owner w j).castSucc = w.val.get ⟨j.val, by rw [ownerWord_length w]; exact j.isLt⟩ := by
  apply Fin.ext
  rfl

lemma owner_idxOf {m T : ℕ} (w : OwnerWords m T) (j : Fin T) :
    w.val.idxOf (owner w j).castSucc = j.val := by
  rw [owner_cast]
  exact List.get_idxOf (ownerWord_nodup w) _

lemma owner_mem_iff {m T : ℕ} (w : OwnerWords m T) (a : Fin m) :
    a.castSucc ∈ w.val ↔ ∃ j, owner w j = a := by
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    let j : Fin T := ⟨i.val, by simpa only [ownerWord_length w] using i.isLt⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    have hh := congrArg Fin.val hi
    exact hh
  · rintro ⟨j, rfl⟩
    rw [owner_cast]
    exact List.get_mem _ _

lemma owner_discovery_bound (g T b : ℕ) (q : List Bool → Fin (g + 1)) :
    ((g : ℝ) - T + 1) * (∑ w : OwnerWords g T, (discoveries (g + 1) b q w.val : ℝ)) ≤
      2 * b * Fintype.card (OwnerWords g T) := by
  have hh := discovery_total_bound (g + 1) b T q (ownerPool g) ((g : ℝ) - T + 1)
    (by rw [ownerPool_card]; ring_nf; exact le_rfl)
  rw [Finset.sum_coe_sort (words (ownerPool g) T) (fun w => (discoveries (g + 1) b q w : ℝ))]
  simpa only [Fintype.card_coe] using hh

lemma owner_discovery_half (g T b : ℕ) (hT : 2 * T ≤ g) (q : List Bool → Fin (g + 1)) :
    (g : ℝ) * (∑ w : OwnerWords g T, (discoveries (g + 1) b q w.val : ℝ)) ≤
      4 * b * Fintype.card (OwnerWords g T) := by
  have hh := owner_discovery_bound g T b q
  have hTR : 2 * (T : ℝ) ≤ g := by exact_mod_cast hT
  have hsum : 0 ≤ ∑ w : OwnerWords g T, (discoveries (g + 1) b q w.val : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right (show (g : ℝ) ≤ 2 * (g - T + 1) by linarith) hsum
  nlinarith only [hh, hm]

end LongTails.Proofs.InterpolatedFiniteSumDistinctSearch
