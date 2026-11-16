import LongTails.Proofs.LocalizedMonotoneProfile

open scoped BigOperators

namespace LongTails.Proofs.LocalizedMonotoneChain

lemma trajectory_error (H : ℝ → ℝ)
    (hH : ∀ x y, |H x - H y| ≤ |x - y|) (s : ℕ → ℝ) (n : ℕ) :
    |s n - H^[n] (s 0)| ≤ ∑ i ∈ Finset.range n, |s (i + 1) - H (s i)| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    calc
      |s (n + 1) - H (H^[n] (s 0))| ≤
          |s (n + 1) - H (s n)| + |H (s n) - H (H^[n] (s 0))| :=
        abs_sub_le _ _ _
      _ ≤ |s (n + 1) - H (s n)| + |s n - H^[n] (s 0)| :=
        add_le_add le_rfl (hH _ _)
      _ ≤ _ := by linarith

lemma iterate_nonneg (H : ℝ → ℝ) (hH : Monotone H) (h0 : H 0 = 0)
    (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ H^[n] x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simpa only [h0] using hH ih

lemma iterate_nonpos (H : ℝ → ℝ) (hH : Monotone H) (h0 : H 0 = 0)
    (x : ℝ) (hx : x ≤ 0) (n : ℕ) : H^[n] x ≤ 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simpa only [h0] using hH ih

lemma negative_wrap_initial_bound (H : ℝ → ℝ) (hmono : Monotone H)
    (h0 : H 0 = 0) (hH : ∀ x y, |H x - H y| ≤ |x - y|)
    (s : ℕ → ℝ) (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    |s 0| ≤ c + |s 0 + H (s n) - c| +
      ∑ i ∈ Finset.range n, |s (i + 1) - H (s i)| := by
  have ht := trajectory_error H hH s n
  have he : |s 0 + H (H^[n] (s 0)) - c| ≤
      |s 0 + H (s n) - c| + ∑ i ∈ Finset.range n, |s (i + 1) - H (s i)| := by
    calc
      _ ≤ |s 0 + H (s n) - c| + |H (H^[n] (s 0)) - H (s n)| := by
        convert abs_add_le (s 0 + H (s n) - c)
          (H (H^[n] (s 0)) - H (s n)) using 1
        congr 1
        ring
      _ ≤ |s 0 + H (s n) - c| + |H^[n] (s 0) - s n| :=
        add_le_add le_rfl (hH _ _)
      _ ≤ _ := add_le_add le_rfl (by simpa only [abs_sub_comm] using ht)
  rcases le_total 0 (s 0) with hs | hs
  · have hp := iterate_nonneg H hmono h0 (s 0) hs (n + 1)
    rw [Function.iterate_succ_apply'] at hp
    rw [abs_of_nonneg hs]
    linarith [(abs_le.mp he).2]
  · have hp := iterate_nonpos H hmono h0 (s 0) hs (n + 1)
    rw [Function.iterate_succ_apply'] at hp
    rw [abs_of_nonpos hs]
    linarith [(abs_le.mp he).1]

lemma iterate_abs_le (H : ℝ → ℝ) (h0 : H 0 = 0)
    (hH : ∀ x y, |H x - H y| ≤ |x - y|) (x : ℝ) (n : ℕ) :
    |H^[n] x| ≤ |x| := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := hH (H^[n] x) 0
    simp only [h0, sub_zero] at h
    exact h.trans ih

lemma negative_wrap_coordinate_bound (H : ℝ → ℝ) (hmono : Monotone H)
    (h0 : H 0 = 0) (hH : ∀ x y, |H x - H y| ≤ |x - y|)
    (s : ℕ → ℝ) (n : ℕ) (c : ℝ) (hc : 0 ≤ c) (i : ℕ) (hi : i ≤ n) :
    |s i| ≤ c + 2 * (|s 0 + H (s n) - c| +
      ∑ j ∈ Finset.range n, |s (j + 1) - H (s j)|) := by
  have hs := negative_wrap_initial_bound H hmono h0 hH s n c hc
  have ht := trajectory_error H hH s i
  have hm : (∑ j ∈ Finset.range i, |s (j + 1) - H (s j)|) ≤
      ∑ j ∈ Finset.range n, |s (j + 1) - H (s j)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (fun j _ _ => abs_nonneg _)
  have hb := iterate_abs_le H h0 hH (s 0) i
  have ha : |s i| ≤ |s i - H^[i] (s 0)| + |H^[i] (s 0)| := by
    simpa only [sub_add_cancel] using abs_add_le (s i - H^[i] (s 0)) (H^[i] (s 0))
  linarith [abs_nonneg (s 0 + H (s n) - c)]

lemma negative_wrap_sum (H : ℝ → ℝ) (s : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    (s 0 + H (s n) - c) + (∑ i ∈ Finset.range n, (s (i + 1) - H (s i))) =
      s n + H (s n) - c + ∑ i ∈ Finset.range n, (s i - H (s i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linarith

lemma negative_wrap_terminal_bound (H : ℝ → ℝ) (s : ℕ → ℝ) (n : ℕ)
    (a b c : ℝ) (hgap : ∀ x, x - H x ≤ b) (hflat : H (s n) = 0)
    (hs : s n ≤ a) :
    (s 0 + H (s n) - c) + (∑ i ∈ Finset.range n, (s (i + 1) - H (s i))) ≤
      a - c + n * b := by
  rw [negative_wrap_sum, hflat, add_zero]
  have hsum : (∑ i ∈ Finset.range n, (s i - H (s i))) ≤ n * b := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, b := Finset.sum_le_sum (fun i _ => hgap (s i))
      _ = _ := by simp
  linarith

end LongTails.Proofs.LocalizedMonotoneChain
