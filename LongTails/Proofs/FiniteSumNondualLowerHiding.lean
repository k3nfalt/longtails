import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators

namespace LongTails.Proofs.FiniteSumNondualLowerHiding

variable {ι : Type*} [DecidableEq ι]

def distinctWords : ℕ → Finset ι → Finset (List ι)
  | 0, _ => {[]}
  | k + 1, s => (s.sigma (fun i => distinctWords k (s.erase i))).image (fun p => p.1 :: p.2)

omit [DecidableEq ι] in
lemma cons_injective : Function.Injective (fun p : Σ _ : ι, List ι => p.1 :: p.2) := by
  intro ⟨a, w⟩ ⟨b, v⟩ h
  obtain ⟨rfl, rfl⟩ := List.cons.inj h
  rfl

lemma distinctWords_sum (k : ℕ) (s : Finset ι) (f : List ι → ℝ) :
    (∑ w ∈ distinctWords (k + 1) s, f w) =
      ∑ i ∈ s, ∑ w ∈ distinctWords k (s.erase i), f (i :: w) := by
  rw [distinctWords, Finset.sum_image]
  · exact Finset.sum_sigma _ _ _
  · intro x _ y _ h
    exact cons_injective h

lemma distinctWords_card (k : ℕ) (s : Finset ι) :
    (distinctWords k s).card = s.card.descFactorial k := by
  induction k generalizing s with
  | zero => simp [distinctWords]
  | succ k ih =>
    rw [distinctWords, Finset.card_image_of_injective _ cons_injective, Finset.card_sigma]
    have he : (∑ i ∈ s, (distinctWords k (s.erase i)).card) =
        s.card * (s.card - 1).descFactorial k := by
      calc
        _ = ∑ _ ∈ s, (s.card - 1).descFactorial k := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ih, Finset.card_erase_of_mem hi]
        _ = _ := by simp
    rw [he]
    cases hc : s.card with
    | zero => simp
    | succ r => simp only [Nat.add_sub_cancel, Nat.succ_descFactorial_succ]

lemma mem_distinctWords (k : ℕ) (s : Finset ι) (w : List ι) :
    w ∈ distinctWords k s ↔ w.length = k ∧ w.Nodup ∧ ∀ i ∈ w, i ∈ s := by
  induction k generalizing s w with
  | zero => cases w <;> simp [distinctWords]
  | succ k ih =>
    cases w with
    | nil => simp [distinctWords, Finset.mem_image]
    | cons a w =>
      simp only [distinctWords, Finset.mem_image, Sigma.exists, Finset.mem_sigma,
        List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff, List.nodup_cons,
        List.forall_mem_cons, ih]
      constructor
      · rintro ⟨i, v, ⟨hi, hv, hn, hm⟩, hi₁, hv₁⟩
        subst i
        subst v
        refine ⟨hv, ⟨?_, hn⟩, hi, ?_⟩
        · intro h
          exact (Finset.mem_erase.mp (hm a h)).1 rfl
        · intro j hj
          exact (Finset.mem_erase.mp (hm j hj)).2
      · rintro ⟨hw, ⟨ha, hn⟩, hs, hm⟩
        refine ⟨a, w, ⟨hs, hw, hn, ?_⟩, rfl, rfl⟩
        intro j hj
        exact Finset.mem_erase.mpr ⟨by intro he; exact ha (he ▸ hj), hm j hj⟩

def hits (B : Finset ι) (w : List ι) : ℕ := w.countP (fun i => decide (i ∈ B))

lemma hits_cons (B : Finset ι) (i : ι) (w : List ι) :
    hits B (i :: w) = (if i ∈ B then 1 else 0) + hits B w := by
  by_cases hi : i ∈ B <;> simp [hits, hi, add_comm]

lemma hits_sum_bound (k : ℕ) (s B : Finset ι) (C D : ℝ)
    (hC : (B.card : ℝ) ≤ C) (hD : 0 ≤ D) (hDs : D + k ≤ s.card) :
    D * (∑ w ∈ distinctWords k s, (hits B w : ℝ)) ≤
      (k : ℝ) * C * (distinctWords k s).card := by
  have hC₀ : 0 ≤ C := (Nat.cast_nonneg _).trans hC
  induction k generalizing s with
  | zero => simp [distinctWords, hits]
  | succ k ih =>
    let M : ℝ := ((s.card - 1).descFactorial k : ℕ)
    have hM : 0 ≤ M := Nat.cast_nonneg _
    have hm (i : ι) (hi : i ∈ s) : ((distinctWords k (s.erase i)).card : ℝ) = M := by
      rw [distinctWords_card, Finset.card_erase_of_mem hi]
    have hc : ((distinctWords (k + 1) s).card : ℝ) = (s.card : ℝ) * M := by
      have he := distinctWords_sum k s (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at he
      rw [he]
      calc
        _ = ∑ _ ∈ s, M := Finset.sum_congr rfl (fun i hi => hm i hi)
        _ = _ := by simp
    have hh : (∑ i ∈ s, if i ∈ B then M else 0) ≤ C * M := by
      have hcard : (s.filter (fun i => i ∈ B)).card ≤ B.card :=
        Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)
      have hcardR : ((s.filter (fun i => i ∈ B)).card : ℝ) ≤ C :=
        (by exact_mod_cast hcard : ((s.filter (fun i => i ∈ B)).card : ℝ) ≤ B.card).trans hC
      rw [← Finset.sum_filter]
      simpa using mul_le_mul_of_nonneg_right hcardR hM
    have hi (i : ι) (hi : i ∈ s) :
        D * (∑ w ∈ distinctWords k (s.erase i), (hits B w : ℝ)) ≤ (k : ℝ) * C * M := by
      have he : ((s.erase i).card : ℝ) + 1 = s.card := by
        exact_mod_cast Finset.card_erase_add_one hi
      have hd : D + (k : ℝ) ≤ (s.erase i).card := by
        simp only [Nat.cast_succ] at hDs
        linarith
      simpa only [hm i hi] using ih (s.erase i) hd
    have hsum := Finset.sum_le_sum (fun i hi' => hi i hi')
    have htail : D * (∑ i ∈ s, ∑ w ∈ distinctWords k (s.erase i), (hits B w : ℝ)) ≤
        (s.card : ℝ) * ((k : ℝ) * C * M) := by
      simpa only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
        mul_assoc, mul_comm, mul_left_comm] using hsum
    have he : (∑ w ∈ distinctWords (k + 1) s, (hits B w : ℝ)) =
        (∑ i ∈ s, if i ∈ B then M else 0) +
        ∑ i ∈ s, ∑ w ∈ distinctWords k (s.erase i), (hits B w : ℝ) := by
      rw [distinctWords_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi'
      by_cases hb : i ∈ B <;>
        simp [hits_cons, hb, Finset.sum_add_distrib, hm i hi']
    rw [he, hc]
    have hd : D ≤ (s.card : ℝ) := by
      simp only [Nat.cast_succ] at hDs
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    have hhead := mul_le_mul_of_nonneg_left hh hD
    have hscale := mul_le_mul_of_nonneg_right hd (mul_nonneg hC₀ hM)
    simp only [Nat.cast_succ]
    nlinarith only [htail, hhead, hscale]

inductive ExposureTree (ι : Type*) (C : ℝ) where
  | leaf (B : Finset ι) (bound : (B.card : ℝ) ≤ C)
  | reveal (next : ι → ExposureTree ι C)

def exposedBad {C : ℝ} : ExposureTree ι C → List ι → Bool
  | .leaf B _, w => decide (0 < hits B w)
  | .reveal _, [] => false
  | .reveal next, i :: w => exposedBad (next i) w

lemma exposedBad_leaf_le_hits {C : ℝ} (B : Finset ι) (hB : (B.card : ℝ) ≤ C)
    (w : List ι) : (if exposedBad (.leaf B hB) w then (1 : ℝ) else 0) ≤ hits B w := by
  by_cases hh : 0 < hits B w
  · simp only [exposedBad, hh, decide_true, ite_true]
    exact_mod_cast hh
  · simp [exposedBad, hh]

lemma tree_bad_sum_bound {C : ℝ} (tree : ExposureTree ι C) (hC : 0 ≤ C)
    (k : ℕ) (s : Finset ι) (D : ℝ) (hD : 0 ≤ D) (hDs : D + k ≤ s.card) :
    D * (∑ w ∈ distinctWords k s, if exposedBad tree w then (1 : ℝ) else 0) ≤
      (k : ℝ) * C * (distinctWords k s).card := by
  induction tree generalizing k s with
  | leaf B hB =>
    have hs := Finset.sum_le_sum (fun w (_ : w ∈ distinctWords k s) =>
      exposedBad_leaf_le_hits B hB w)
    exact (mul_le_mul_of_nonneg_left hs hD).trans (hits_sum_bound k s B C D hB hD hDs)
  | reveal next ih =>
    cases k with
    | zero => simp only [distinctWords, Finset.sum_singleton, exposedBad, Bool.false_eq_true,
        ↓reduceIte, mul_zero, Nat.cast_zero, zero_mul, le_refl]
    | succ k =>
      have hc : ((distinctWords (k + 1) s).card : ℝ) =
          ∑ i ∈ s, ((distinctWords k (s.erase i)).card : ℝ) := by
        norm_cast
        rw [distinctWords, Finset.card_image_of_injective _ cons_injective, Finset.card_sigma]
      rw [distinctWords_sum]
      simp only [exposedBad]
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ i ∈ s, (((k : ℝ) + 1) * C * (distinctWords k (s.erase i)).card) := by
          apply Finset.sum_le_sum
          intro i hi
          have he : ((s.erase i).card : ℝ) + 1 = s.card := by
            exact_mod_cast Finset.card_erase_add_one hi
          have hd : D + (k : ℝ) ≤ (s.erase i).card := by
            simp only [Nat.cast_succ] at hDs
            linarith
          have hb := ih i k (s.erase i) hd
          have hn : (0 : ℝ) ≤ (distinctWords k (s.erase i)).card := Nat.cast_nonneg _
          exact hb.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) ≤ k + 1) hC) hn)
        _ = _ := by rw [← Finset.mul_sum, ← hc]; simp

lemma tree_bad_count_bound {C : ℝ} (tree : ExposureTree ι C) (hC : 0 ≤ C)
    (k : ℕ) (s : Finset ι) (D : ℝ) (hD : 0 ≤ D) (hDs : D + k ≤ s.card) :
    D * (((distinctWords k s).filter (fun w => exposedBad tree w)).card : ℝ) ≤
      (k : ℝ) * C * (distinctWords k s).card := by
  have h := tree_bad_sum_bound tree hC k s D hD hDs
  rw [← Finset.sum_filter] at h
  simpa using h

lemma tree_family_bad_bound {C : ℝ} {J : Type*} [Fintype J]
    (tree : J → ExposureTree ι C) (hC : 0 ≤ C)
    (k : ℕ) (s : Finset ι) (D : ℝ) (hD : 0 ≤ D) (hDs : D + k ≤ s.card) :
    D * (((distinctWords k s).filter (fun w => ∃ j, exposedBad (tree j) w = true)).card : ℝ) ≤
      (Fintype.card J : ℝ) * k * C * (distinctWords k s).card := by
  classical
  have hp (w : List ι) :
      (if ∃ j, exposedBad (tree j) w = true then (1 : ℝ) else 0) ≤
        ∑ j, if exposedBad (tree j) w then (1 : ℝ) else 0 := by
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      exact (by simp [hj] : (1 : ℝ) = if exposedBad (tree j) w then 1 else 0).le.trans
        (Finset.single_le_sum (f := fun i => if exposedBad (tree i) w then (1 : ℝ) else 0)
          (fun i _ => by split <;> norm_num) (Finset.mem_univ j))
    · exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun w (_ : w ∈ distinctWords k s) => hp w)) hD
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) =>
    tree_bad_sum_bound (tree j) hC k s D hD hDs)
  have hc : (∑ w ∈ distinctWords k s,
      if ∃ j, exposedBad (tree j) w = true then (1 : ℝ) else 0) =
      (((distinctWords k s).filter (fun w => ∃ j, exposedBad (tree j) w = true)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hc, Finset.sum_comm] at hs
  rw [Finset.mul_sum] at hs
  exact hs.trans (by simpa [mul_assoc] using hb)

end LongTails.Proofs.FiniteSumNondualLowerHiding
