import LongTails.Proofs.BirchCausalCoefficients

namespace LongTails.Proofs.BirchRetainedWork

open Finset

noncomputable def residual (a : ℝ) (β c : ℕ → ℝ) (n : ℕ) : ℝ :=
  a - ∑ j ∈ range n, β j * c j

lemma residual_zero (a : ℝ) (β c : ℕ → ℝ) : residual a β c 0 = a := by
  simp [residual]

lemma residual_succ (a : ℝ) (β c : ℕ → ℝ) (n : ℕ) :
    residual a β c (n + 1) = residual a β c n - β n * c n := by
  simp only [residual, sum_range_succ]
  ring

lemma segment_retention (u p : ℕ → ℝ) (start count : ℕ)
    (hp : ∀ j, 0 ≤ p j)
    (hstep : ∀ j, start ≤ j → j < start + count → p j * u j ≤ u (j + 1)) :
    (∏ j ∈ range count, p (start + j)) * u start ≤ u (start + count) := by
  induction count with
  | zero => simp
  | succ count ih =>
      have ih' := ih (fun j hj hj' => hstep j hj (by omega))
      have hm := mul_le_mul_of_nonneg_left ih' (hp (start + count))
      have hs := hstep (start + count) (by omega) (by omega)
      simpa [prod_range_succ, Nat.add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using hm.trans hs

lemma depletion_bounds (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (active : ℕ → Prop) [DecidablePred active] (a : ℝ) (β scale c : ℕ → ℝ)
    (ha : 0 ≤ a) (hβ : ∀ n, 0 ≤ β n) (hscale : ∀ n, 1 ≤ scale n)
    (hp : ∀ n, 0 ≤ 1 - β n * scale n)
    (hpast : ∀ n, history n ⊆ range n)
    (hfrontier : ∀ n, frontier n ≤ n)
    (hprefix : ∀ n, range (frontier n) ⊆ history n)
    (hgate : ∀ n, 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hrec : ∀ n, c n = if active n then a - ∑ j ∈ history n, β j * c j else 0) :
    ∀ n, 0 ≤ residual a β c n ∧ 0 ≤ c n ∧ c n ≤ a ∧
      c n ≤ scale n * residual a β c n ∧
      (1 - β n * scale n) * residual a β c n ≤ residual a β c (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hu : 0 ≤ residual a β c n := by
        cases n with
        | zero => simpa [residual] using ha
        | succ n =>
            exact (mul_nonneg (hp n) (ih n (by omega)).1).trans
              (ih n (by omega)).2.2.2.2
      have hcprior : ∀ j ∈ range n, 0 ≤ c j := by
        intro j hj
        exact (ih j (mem_range.mp hj)).2.1
      have hterms : ∀ j ∈ range n, 0 ≤ β j * c j :=
        fun j hj => mul_nonneg (hβ j) (hcprior j hj)
      have hsum : 0 ≤ ∑ j ∈ history n, β j * c j :=
        sum_nonneg (fun j hj => hterms j (hpast n hj))
      have hfull : (∑ j ∈ history n, β j * c j) ≤ ∑ j ∈ range n, β j * c j :=
        sum_le_sum_of_subset_of_nonneg (hpast n) (fun j hj _ => hterms j hj)
      have hpre : (∑ j ∈ range (frontier n), β j * c j) ≤
          ∑ j ∈ history n, β j * c j :=
        sum_le_sum_of_subset_of_nonneg (hprefix n)
          (fun j hj _ => hterms j (hpast n hj))
      have hul : 0 ≤ residual a β c (frontier n) := by
        by_cases he : frontier n = n
        · simpa [he] using hu
        · exact (ih (frontier n) (lt_of_le_of_ne (hfrontier n) he)).1
      have hsegment := segment_retention (residual a β c)
        (fun j => 1 - β j * scale j) (frontier n) (n - frontier n) hp
        (fun j _ hj => (ih j (by omega)).2.2.2.2)
      rw [Nat.add_sub_of_le (hfrontier n)] at hsegment
      have hratio : residual a β c (frontier n) ≤ scale n * residual a β c n := by
        have hg := mul_le_mul_of_nonneg_right (hgate n) hul
        have hs := mul_le_mul_of_nonneg_left hsegment (by linarith [hscale n])
        nlinarith
      have hc : 0 ≤ c n ∧ c n ≤ a ∧ c n ≤ scale n * residual a β c n := by
        rw [hrec n]
        split_ifs
        · have hlo : residual a β c n ≤ a - ∑ j ∈ history n, β j * c j := by
            dsimp [residual]
            linarith
          have hhi : a - ∑ j ∈ history n, β j * c j ≤
              residual a β c (frontier n) := by
            dsimp [residual]
            linarith
          exact ⟨hu.trans hlo, by linarith, hhi.trans hratio⟩
        · exact ⟨le_rfl, ha, mul_nonneg (by linarith [hscale n]) hu⟩
      refine ⟨hu, hc.1, hc.2.1, hc.2.2, ?_⟩
      rw [residual_succ]
      nlinarith [mul_le_mul_of_nonneg_left hc.2.2 (hβ n)]

lemma residual_antitone (a : ℝ) (β c : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (hc : ∀ n, 0 ≤ c n) : Antitone (residual a β c) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [residual_succ]
  exact sub_le_self _ (mul_nonneg (hβ n) (hc n))

lemma depletion_tail (history : ℕ → Finset ℕ) (a : ℝ) (β c : ℕ → ℝ)
    (cutoff : ℕ) (hβ : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n ≤ 1)
    (hpast : ∀ n, history n ⊆ range n) (hc : ∀ n, 0 ≤ c n)
    (hrec : ∀ n, cutoff ≤ n → c n = a - ∑ j ∈ history n, β j * c j) :
    ∀ count, residual a β c (cutoff + count) ≤
      (∏ j ∈ range count, (1 - β (cutoff + j))) * residual a β c cutoff := by
  have hstep (n : ℕ) (hn : cutoff ≤ n) :
      residual a β c (n + 1) ≤ (1 - β n) * residual a β c n := by
    have hs : (∑ j ∈ history n, β j * c j) ≤ ∑ j ∈ range n, β j * c j :=
      sum_le_sum_of_subset_of_nonneg (hpast n)
        (fun j _ _ => mul_nonneg (hβ j) (hc j))
    have hlo : residual a β c n ≤ c n := by
      rw [hrec n hn]
      dsimp [residual]
      linarith
    rw [residual_succ]
    nlinarith [mul_le_mul_of_nonneg_left hlo (hβ n)]
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hβ1 (cutoff + count)))
      have hs := hstep (cutoff + count) (by omega)
      simpa [Nat.add_assoc, prod_range_succ, mul_comm, mul_left_comm, mul_assoc]
        using hs.trans hm

lemma masked_tail (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (a : ℝ) (β scale c : ℕ → ℝ) (cutoff : ℕ)
    (ha : 0 ≤ a) (hβ : ∀ n, 0 ≤ β n) (hscale : ∀ n, 1 ≤ scale n)
    (hp : ∀ n, 0 ≤ 1 - β n * scale n)
    (hpast : ∀ n, history n ⊆ range n)
    (hfrontier : ∀ n, frontier n ≤ n)
    (hprefix : ∀ n, range (frontier n) ⊆ history n)
    (hgate : ∀ n, 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hrec : ∀ n, c n = if cutoff ≤ n then a - ∑ j ∈ history n, β j * c j else 0)
    (n : ℕ) (hn : cutoff ≤ n) :
    c n ≤ scale n * a * ∏ j ∈ range (n - cutoff), (1 - β (cutoff + j)) := by
  have hb := depletion_bounds history frontier (cutoff ≤ ·) a β scale c
    ha hβ hscale hp hpast hfrontier hprefix hgate hrec
  have hβ1 : ∀ j, β j ≤ 1 := by
    intro j
    nlinarith [hp j, mul_le_mul_of_nonneg_left (hscale j) (hβ j)]
  have hu : residual a β c cutoff = a := by
    have hz : (∑ j ∈ range cutoff, β j * c j) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [hrec j, ite_eq_right (by have := mem_range.mp hj; omega), mul_zero]
    simp [residual, hz]
  have ht := depletion_tail history a β c cutoff hβ hβ1 hpast
    (fun j => (hb j).2.1) (fun j hj => by simpa [hj] using hrec j) (n - cutoff)
  rw [Nat.add_sub_of_le hn, hu] at ht
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ scale n by linarith [hscale n])
  exact (hb n).2.2.2.1.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hm)

noncomputable def survival (β : ℕ → ℝ) (start stop : ℕ) : ℝ :=
  ∏ j ∈ Ico start stop, (1 - β j)

lemma survival_self (β : ℕ → ℝ) (n : ℕ) : survival β n n = 1 := by
  simp [survival]

lemma survival_succ_right (β : ℕ → ℝ) (start n : ℕ) (hn : start ≤ n) :
    survival β start (n + 1) = survival β start n * (1 - β n) := by
  exact prod_Ico_succ_top hn _

lemma survival_nonnegative (β : ℕ → ℝ) (hβ1 : ∀ j, β j ≤ 1) (start stop : ℕ) :
    0 ≤ survival β start stop :=
  prod_nonneg (fun j _ => sub_nonneg.mpr (hβ1 j))

lemma survival_le_one (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hβ1 : ∀ j, β j ≤ 1) (start stop : ℕ) : survival β start stop ≤ 1 :=
  prod_le_one₀ (fun j _ => sub_nonneg.mpr (hβ1 j))
    (fun j _ => sub_le_self _ (hβ j))

lemma forward_occupation (β : ℕ → ℝ) (start count : ℕ) :
    (∑ j ∈ range count, β (start + j) * survival β start (start + j)) =
      1 - survival β start (start + count) := by
  induction count with
  | zero => simp [survival]
  | succ count ih =>
      rw [sum_range_succ, ih]
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        survival_succ_right β start (start + count) (by omega)]
      ring

lemma forward_occupation_le_one (β : ℕ → ℝ) (hβ1 : ∀ j, β j ≤ 1)
    (start count : ℕ) :
    (∑ j ∈ range count, β (start + j) * survival β start (start + j)) ≤ 1 := by
  rw [forward_occupation]
  exact sub_le_self _ (survival_nonnegative β hβ1 _ _)

lemma reverse_occupation (β : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, β j * survival β (j + 1) n) = 1 - survival β 0 n := by
  induction n with
  | zero => simp [survival]
  | succ n ih =>
      rw [sum_range_succ]
      have hs : (∑ j ∈ range n, β j * survival β (j + 1) (n + 1)) =
          (∑ j ∈ range n, β j * survival β (j + 1) n) * (1 - β n) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro j hj
        rw [survival_succ_right β (j + 1) n (by have := mem_range.mp hj; omega)]
        ring
      rw [hs, ih, survival_self, survival_succ_right β 0 n (by omega)]
      ring

lemma reverse_occupation_le_one (β : ℕ → ℝ) (hβ1 : ∀ j, β j ≤ 1) (n : ℕ) :
    (∑ j ∈ range n, β j * survival β (j + 1) n) ≤ 1 := by
  rw [reverse_occupation]
  exact sub_le_self _ (survival_nonnegative β hβ1 _ _)

lemma survival_range (β : ℕ → ℝ) (start count : ℕ) :
    survival β start (start + count) =
      ∏ j ∈ range count, (1 - β (start + j)) := by
  induction count with
  | zero => simp [survival]
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        survival_succ_right β start (start + count) (by omega), ih, prod_range_succ]

lemma survival_zero_of_reset (β : ℕ → ℝ) (start stop reset : ℕ)
    (hr : reset ∈ Ico start stop) (hreset : β reset = 1) :
    survival β start stop = 0 := by
  exact prod_eq_zero hr (by simp [hreset])

end LongTails.Proofs.BirchRetainedWork
