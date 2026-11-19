import LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
import LongTails.Proofs.DistributedJacobianStrongGrowthMedian

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianSearch

open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch

lemma binarySearch_eq (test : ℕ → Bool) (m w lo : ℕ)
    (htest : ∀ t, test t = true ↔ m < t)
    (hlo : lo ≤ m) (hhi : m < lo + 2 ^ w) : binarySearch test w lo = m := by
  induction w generalizing lo with
  | zero => simp only [binarySearch]; norm_num at hhi; omega
  | succ w ih =>
      have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by simp [pow_succ, Nat.mul_two]
      rw [hpow] at hhi
      unfold binarySearch
      by_cases hmid : m < lo + 2 ^ w
      · rw [ite_eq_left ((htest _).mpr hmid)]
        exact ih lo hlo hmid
      · have hfalse : ¬ test (lo + 2 ^ w) = true := by rw [htest]; exact hmid
        rw [ite_eq_right hfalse]
        exact ih (lo + 2 ^ w) (by omega) (by omega)

lemma sorted_count_threshold {α : Type*} [LinearOrder α] (l : List α)
    (hs : l.SortedLE) (k : ℕ) (hk : k < l.length) (t : α) :
    k < l.countP (fun x => decide (x < t)) ↔ l[k] < t := by
  let pred : α → Bool := fun x => decide (x < t)
  constructor
  · intro hcount
    by_contra hnot
    have hz : (l.drop k).countP pred = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hil : k + i < l.length := by simp only [List.length_drop] at hi; omega
      have hv := hs.getElem_le_getElem_of_le (hi := hk) (hj := hil) (Nat.le_add_right k i)
      have he' : l[k + i] = x := by simpa using he
      rw [he'] at hv
      simp only [pred, decide_eq_true_eq]
      intro hxt
      exact hnot (hv.trans_lt hxt)
    have hc := List.countP_le_length (p := pred) (l := l.take k)
    have he := List.countP_append (p := pred) (l₁ := l.take k) (l₂ := l.drop k)
    rw [List.take_append_drop, hz, add_zero] at he
    rw [← he, List.length_take] at hc
    change k < l.countP pred at hcount
    omega
  · intro hlt
    have hall : (l.take (k + 1)).countP pred = (l.take (k + 1)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hil : i < l.length := by simp only [List.length_take] at hi; omega
      have hik : i ≤ k := by simp only [List.length_take] at hi; omega
      have hv := hs.getElem_le_getElem_of_le (hi := hil) (hj := hk) hik
      have he' : l[i] = x := by simpa using he
      rw [he'] at hv
      exact decide_eq_true (hv.trans_lt hlt)
    have he := List.countP_append (p := pred) (l₁ := l.take (k + 1)) (l₂ := l.drop (k + 1))
    rw [List.take_append_drop, hall, List.length_take] at he
    change k < l.countP pred
    omega

lemma countBelow_le {n d width : ℕ}
    (codes : Fin n → LongTails.Algorithms.DistributedQuantization.Grid d width)
    (j : Fin d) (threshold : ℕ) : countBelow codes j threshold ≤ n := by
  unfold countBelow
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
    _ = n := by simp

lemma countBelow_eq_countP {n d width : ℕ}
    (codes : Fin n → LongTails.Algorithms.DistributedQuantization.Grid d width)
    (j : Fin d) (threshold : ℕ) :
    countBelow codes j threshold =
      (List.ofFn (fun i => codes i j)).countP (fun x => decide (x.val < threshold)) := by
  have hh := OracleTemplate.AdaptiveHeavyTailSimplex.countP_ofFn_real
    (fun x : Fin (2 ^ width) => decide (x.val < threshold)) n (fun i => codes i j)
  have hc : ((countBelow codes j threshold : ℕ) : ℝ) =
      ∑ i : Fin n, if (codes i j).val < threshold then (1 : ℝ) else 0 := by
    simp [countBelow]
  simp only [decide_eq_true_eq] at hh
  exact_mod_cast (hc.trans hh.symm)

lemma median_threshold {n d width : ℕ} (hn : 0 < n)
    (codes : Fin n → LongTails.Algorithms.DistributedQuantization.Grid d width)
    (j : Fin d) (threshold : ℕ) :
    n / 2 < countBelow codes j threshold ↔
      (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val < threshold := by
  let values := List.ofFn (fun i => codes i j)
  let sorted := values.mergeSort (· ≤ ·)
  have hperm : sorted.Perm values := List.mergeSort_perm _ _
  have hlen : sorted.length = n := by rw [hperm.length_eq]; simp [values]
  have hsorted : (sorted.map Fin.val).SortedLE := by
    apply List.Pairwise.sortedLE
    apply List.pairwise_map.mpr
    exact (List.sortedLE_mergeSort (l := values)).pairwise.imp (fun h => h)
  have hk : n / 2 < sorted.length := by rw [hlen]; omega
  have hkmap : n / 2 < (sorted.map Fin.val).length := by simpa using hk
  have hh := sorted_count_threshold (sorted.map Fin.val) hsorted (n / 2) hkmap threshold
  have hc : (sorted.map Fin.val).countP (fun x => decide (x < threshold)) =
      countBelow codes j threshold := by
    rw [List.countP_map, hperm.countP_eq, countBelow_eq_countP]
    rfl
  have he : (sorted.map Fin.val)[n / 2] =
      (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val := by
    rw [← List.getD_eq_getElem _ 0 hkmap]
    change (sorted.map Fin.val).getD (n / 2) (Fin.val (0 : Fin (2 ^ width))) = _
    rw [List.getD_map]
    rfl
  rwa [hc, he] at hh

lemma medianCode_eq {n d width : ℕ} (hn : 0 < n)
    (codes : Fin n → LongTails.Algorithms.DistributedQuantization.Grid d width) (j : Fin d) :
    medianCode codes j =
      (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val := by
  apply binarySearch_eq
  · intro t
    simp only [decide_eq_true_eq]
    exact median_threshold hn codes j t
  · exact Nat.zero_le _
  · simpa only [Nat.zero_add] using
      (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).isLt

lemma countBelow_fits {n d width : ℕ}
    (codes : Fin n → LongTails.Algorithms.DistributedQuantization.Grid d width)
    (j : Fin d) (threshold : ℕ) : countBelow codes j threshold < 2 ^ countWidth n := by
  exact (countBelow_le codes j threshold).trans_lt Nat.lt_log2_self

lemma nextLower_interval {d : ℕ} (remaining : ℕ) (lo target : Fin d → ℕ)
    (decisions : Fin d → Bool)
    (hlo : ∀ j, lo j ≤ target j)
    (hhi : ∀ j, target j < lo j + 2 ^ (remaining + 1))
    (htest : ∀ j, decisions j = true ↔ target j < lo j + 2 ^ remaining) :
    (∀ j, nextLower remaining lo decisions j ≤ target j) ∧
      (∀ j, target j < nextLower remaining lo decisions j + 2 ^ remaining) := by
  have hpow : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    simp [pow_succ, Nat.mul_two]
  constructor <;> intro j
  · by_cases hj : decisions j = true
    · simpa [nextLower, hj] using hlo j
    · have ht := (htest j).not.mp hj
      simp only [nextLower, ite_eq_right hj]
      omega
  · have hi := hhi j
    rw [hpow] at hi
    by_cases hj : decisions j = true
    · simpa [nextLower, hj] using (htest j).mp hj
    · simp only [nextLower, ite_eq_right hj]
      omega

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianSearch
