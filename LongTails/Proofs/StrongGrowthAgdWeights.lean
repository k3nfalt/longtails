import LongTails.Algorithms.StrongGrowthRestartedAgd

namespace LongTails.Proofs.StrongGrowthAgdWeights

open LongTails.Algorithms.StrongGrowthRestartedAgd

lemma sum_range_cast (K : ℕ) : ∑ k ∈ Finset.range K, (k : ℝ) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma pW_eq (K : ℕ) : pW K = ((K : ℝ) ^ 3 - K) / 6 := by
  induction K with
  | zero => simp [pW]
  | succ K ih =>
    unfold pW at ih ⊢
    rw [Finset.sum_range_succ]
    have h : ∑ k ∈ Finset.range K, (k : ℝ) * (((K + 1 : ℕ) : ℝ) - k) =
        ∑ k ∈ Finset.range K, ((k : ℝ) * ((K : ℝ) - k) + k) := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [h, Finset.sum_add_distrib, ih, sum_range_cast]
    push_cast
    ring

lemma four_mul_le_cube {K : ℕ} (hK : 2 ≤ K) : 4 * (K : ℝ) ≤ (K : ℝ) ^ 3 := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h4 : (4 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ K)
  nlinarith

lemma pW_pos {K : ℕ} (hK : 2 ≤ K) : 0 < pW K := by
  rw [pW_eq]
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have := four_mul_le_cube hK
  linarith

lemma pw_nonneg {K k : ℕ} (hK : 2 ≤ K) (hk : k ≤ K) : 0 ≤ pw K k := by
  unfold pw
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (pW_pos hK).le

lemma pw_zero (K : ℕ) : pw K 0 = 0 := by simp [pw]

lemma pw_self (K : ℕ) : pw K K = 0 := by simp [pw]

lemma sum_pw {K : ℕ} (hK : 2 ≤ K) : ∑ k ∈ Finset.range K, pw K k = 1 := by
  unfold pw
  rw [← Finset.sum_div]
  exact div_self (pW_pos hK).ne'

lemma pw_le {K k : ℕ} (hK : 2 ≤ K) : pw K k ≤ 2 / K := by
  unfold pw
  have hP := pW_pos hK
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  rw [div_le_div_iff₀ hP (by linarith), pW_eq]
  have h1 : (k : ℝ) * ((K : ℝ) - k) ≤ (K : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg ((k : ℝ) - K / 2)]
  have h2 := four_mul_le_cube hK
  have h3 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ K)
  nlinarith [sq_nonneg (K : ℝ)]

lemma pw_succ_sub {K k : ℕ} (hK : 3 ≤ K) (hk : k + 1 ≤ K) :
    |pw K (k + 1) - pw K k| ≤ 7 / (K : ℝ) ^ 2 := by
  unfold pw
  have hK2 : 2 ≤ K := by omega
  have hP := pW_pos hK2
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
  rw [← sub_div, abs_div, abs_of_pos hP, div_le_div_iff₀ hP (by positivity), pW_eq]
  have h1 : |((k + 1 : ℕ) : ℝ) * ((K : ℝ) - (k + 1 : ℕ)) - (k : ℝ) * ((K : ℝ) - k)| =
      |(K : ℝ) - 2 * k - 1| := by
    congr 1; push_cast; ring
  rw [h1]
  have h2 : |(K : ℝ) - 2 * k - 1| ≤ K := by
    rw [abs_le]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    constructor <;> linarith
  have h3 : 7 * (K : ℝ) ≤ (K : ℝ) ^ 3 := by
    have h4 : (7 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ K)
    nlinarith
  calc |(K : ℝ) - 2 * k - 1| * (K : ℝ) ^ 2 ≤ K * (K : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ 7 * (((K : ℝ) ^ 3 - K) / 6) := by nlinarith

lemma wsum_succ (K k : ℕ) : ∑ i ∈ Finset.range (k + 1), pw K i = (∑ i ∈ Finset.range k, pw K i) + pw K k :=
  Finset.sum_range_succ _ _

lemma wsum_nonneg {K k : ℕ} (hK : 2 ≤ K) (hk : k ≤ K) : 0 ≤ ∑ i ∈ Finset.range k, pw K i :=
  Finset.sum_nonneg (fun i hi => pw_nonneg hK (by simp at hi; omega))

end LongTails.Proofs.StrongGrowthAgdWeights
