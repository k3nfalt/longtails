import LongTails.Proofs.QuarticAccelerationGrowth

namespace LongTails.Proofs.QuarticAccelerationCount

open Finset

lemma selected_sequence_growth (b : ℕ → ℝ) (up : ℕ → Prop) [DecidablePred up]
    {c : ℝ} (N : ℕ) (hc : 0 < c) (hb : ∀ k ≤ N, 0 ≤ b k)
    (hmono : ∀ k < N, b k ≤ b (k + 1))
    (hbpos : ∀ k < N, up k → 0 < b (k + 1))
    (hrec : ∀ k ≤ N, c * (∑ i ∈ range k, if up i then b (i + 1) else 0) ≤ b k ^ 2) :
    ∀ k ≤ N, c * (∑ i ∈ range k, if up i then (1 : ℝ) else 0) / 2 ≤ b k := by
  let count := fun k => ∑ i ∈ range k, if up i then (1 : ℝ) else 0
  let total := fun k => ∑ i ∈ range k, if up i then b (i + 1) else 0
  have hcount k : 0 ≤ count k := sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have htotal k (hk : k ≤ N) : 0 ≤ total k := sum_nonneg (fun i hi => by split_ifs; exact hb (i + 1) (by have := mem_range.mp hi; omega); norm_num)
  have hind k (hk : k ≤ N) : c * count k / 2 ≤ b k ∧ c * count k * (count k + 1) / 4 ≤ total k := by
    induction k with
    | zero => simpa [count, total] using hb 0 (Nat.zero_le _)
    | succ k ih =>
      have hlt : k < N := by omega
      have ih := ih (by omega : k ≤ N)
      have hec : count (k + 1) = count k + if up k then 1 else 0 := sum_range_succ _ _
      have het : total (k + 1) = total k + if up k then b (k + 1) else 0 := sum_range_succ _ _
      by_cases hu : up k
      · rw [ite_eq_left hu] at hec het
        have hself : c ≤ b (k + 1) := by
          have hh := hrec (k + 1) hk
          change c * total (k + 1) ≤ b (k + 1) ^ 2 at hh
          rw [het] at hh
          have hp := hbpos k hlt hu
          have hn := mul_nonneg hc.le (htotal k hlt.le)
          nlinarith only [hh, hp, hn]
        have hnext : c * count (k + 1) / 2 ≤ b (k + 1) := by
          rw [hec]
          by_contra hnot
          have hlt := lt_of_not_ge hnot
          have hprod := mul_pos (sub_pos.mpr hlt)
            (show 0 < c * (count k + 1) / 2 + b (k + 1) - c by linarith)
          have hh := hrec (k + 1) hk
          change c * total (k + 1) ≤ b (k + 1) ^ 2 at hh
          rw [het] at hh
          have hp := mul_le_mul_of_nonneg_left ih.2 hc.le
          have hpos : 0 < c ^ 2 * (count k + 1) := mul_pos (sq_pos_of_pos hc) (by linarith [hcount k])
          nlinarith only [hh, hp, hprod, hpos]
        refine ⟨hnext, ?_⟩
        rw [hec, het]
        rw [hec] at hnext
        nlinarith only [ih.2, hnext]
      · rw [ite_eq_right hu, add_zero] at hec het
        rw [hec, het]
        exact ⟨ih.1.trans (hmono k hlt), ih.2⟩
  exact fun k hk => (hind k hk).1

lemma step_weight_sum (b t : ℕ → ℝ) (up : ℕ → Prop) [DecidablePred up] (N : ℕ)
    (hstep : ∀ k < N, b (k + 1) = if up k then b k / 2 else 2 * b k)
    (ht0 : 0 ≤ t 0) (hmono : ∀ k < N, t k ≤ t (k + 1))
    (hdown : ∀ k < N, ¬up k → b k ≤ 2 * (t (k + 1) - t k))
    (hbN : 0 ≤ b N) (hinit : b 0 ≤ t N) :
    (∑ k ∈ range N, b k) ≤ 8 * t N := by
  have hid (j : ℕ) (hj : j ≤ N) : (∑ k ∈ range j, b k) + 2 * b j =
      3 * (∑ k ∈ range j, if up k then 0 else b k) + 2 * b 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hlt : j < N := by omega
      have ih := ih hlt.le
      rw [sum_range_succ, sum_range_succ, hstep j hlt]
      split_ifs <;> nlinarith only [ih]
  have hdsum : (∑ k ∈ range N, if up k then (0 : ℝ) else b k) ≤
      ∑ k ∈ range N, 2 * (t (k + 1) - t k) := by
    apply sum_le_sum
    intro k hk
    have hlt : k < N := mem_range.mp hk
    split_ifs with hu
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hmono k hlt))
    · exact hdown k hlt hu
  rw [← mul_sum, sum_range_sub] at hdsum
  nlinarith only [hid N le_rfl, hdsum, hbN, hinit, ht0]

end LongTails.Proofs.QuarticAccelerationCount
