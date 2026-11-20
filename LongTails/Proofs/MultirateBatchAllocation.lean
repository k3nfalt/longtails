import LongTails.Algorithms.MultirateBatches
import Mathlib.Tactic

namespace LongTails.Proofs.MultirateBatchAllocation

open LongTails.Algorithms.MultirateBatches

variable {ι : Type*} [Fintype ι] {h a b : ι → ℝ}

lemma square_sum_pos (i : ι) (ha : a i ≠ 0) : 0 < ∑ j, a j ^ 2 :=
  (sq_pos_of_ne_zero ha).trans_le (Finset.single_le_sum (fun j _ => sq_nonneg (a j))
    (Finset.mem_univ i))

lemma product_sum_pos (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι)
    (hi : 0 < a i * b i) : 0 < ∑ j, a j * b j :=
  hi.trans_le (Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (hb j)) (Finset.mem_univ i))

lemma share_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) : 0 ≤ share a b i := by
  unfold share
  positivity [ha i, hb i, Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => mul_nonneg (ha j) (hb j))]

lemma share_pos (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) (hi : a i ≠ 0) :
    0 < share a b i := by
  have hs := div_pos (sq_pos_of_ne_zero hi) (square_sum_pos i hi)
  have ht := div_nonneg (mul_nonneg (ha i) (hb i))
    (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => mul_nonneg (ha j) (hb j)))
  unfold share
  linarith

lemma sum_share_le_one : (∑ i, share a b i) ≤ 1 := by
  simp only [share, ← Finset.sum_div, Finset.sum_add_distrib]
  linarith [div_self_le_one (∑ i, a i ^ 2), div_self_le_one (∑ i, a i * b i)]

lemma duration_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    duration a b i ≤ 2 * ∑ j, a j ^ 2 := by
  by_cases hi : a i = 0
  · simp [duration, hi, Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (a j))]
  have hs := square_sum_pos i hi
  have ht := div_nonneg (mul_nonneg (ha i) (hb i))
    (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => mul_nonneg (ha j) (hb j)))
  apply (div_le_iff₀ (share_pos ha hb i hi)).mpr
  have hz : a i ^ 2 / (∑ j, a j ^ 2) ≤ 2 * share a b i := by unfold share; linarith
  have he := (div_le_iff₀ hs).mp hz
  linarith only [he]

lemma weighted_duration_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    b i ^ 2 * duration a b i ≤ 2 * (∑ j, a j * b j) * (a i * b i) := by
  by_cases hi : a i = 0
  · simp [duration, hi]
  by_cases hj : b i = 0
  · simp [hj]
  have hab := mul_pos (lt_of_le_of_ne (ha i) (Ne.symm hi)) (lt_of_le_of_ne (hb i) (Ne.symm hj))
  have hs := product_sum_pos ha hb i hab
  have ht := div_nonneg (sq_nonneg (a i)) (square_sum_pos i hi).le
  have hz : a i * b i / (∑ j, a j * b j) ≤ 2 * share a b i := by unfold share; linarith
  have he := mul_le_mul_of_nonneg_right ((div_le_iff₀ hs).mp hz) hab.le
  unfold duration
  rw [← mul_div_assoc, div_le_iff₀ (share_pos ha hb i hi)]
  linarith only [he]

lemma count_lower (hh : ∀ i, 0 < h i) (i : ι) :
    duration a b i ≤ (count h a b i : ℝ) * h i := by
  apply (div_le_iff₀ (hh i)).mp
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

lemma count_upper (hh : ∀ i, 0 < h i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    (count h a b i : ℝ) * h i ≤ h i + duration a b i := by
  have hd : 0 ≤ duration a b i := div_nonneg (sq_nonneg _) (share_nonneg ha hb i)
  have hp := div_nonneg hd (hh i).le
  have hu : (count h a b i : ℝ) ≤ 1 + duration a b i / h i := by
    change ((max 1 ⌈duration a b i / h i⌉₊ : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (le_add_of_nonneg_right hp) ((Nat.ceil_lt_add_one hp).le.trans_eq (add_comm _ _))
  have he := mul_le_mul_of_nonneg_right hu (hh i).le
  rwa [add_mul, one_mul, div_mul_cancel₀ _ (hh i).ne'] at he

lemma variance_budget (hh : ∀ i, 0 < h i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, a i ^ 2 / ((count h a b i : ℝ) * h i)) ≤ 1 := by
  apply le_trans (Finset.sum_le_sum (g := share a b) ?_) sum_share_le_one
  intro i _
  by_cases hi : a i = 0
  · simpa only [hi, zero_pow (by decide : 2 ≠ 0), zero_div] using share_nonneg ha hb i
  have hc : (0 : ℝ) < count h a b i := by exact_mod_cast (count h a b i).pos
  apply (div_le_iff₀ (mul_pos hc (hh i))).mpr
  have he := (div_le_iff₀ (share_pos ha hb i hi)).mp (count_lower (a := a) (b := b) hh i)
  linarith only [he]

end LongTails.Proofs.MultirateBatchAllocation
