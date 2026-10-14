import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

lemma endpoint_difference {A : Type*} [Ring A] (a b c : A) :
    a * b * c - a * b - b * c + b = (a - 1) * b * (c - 1) := by
  noncomm_ring

lemma norm_endpoint_difference {A : Type*} [NormedRing A] (a b c : A)
    {β : ℝ} (ha : ‖a - 1‖ ≤ β) (hb : ‖b‖ ≤ 1) (hc : ‖c - 1‖ ≤ β) :
    ‖a * b * c - a * b - b * c + b‖ ≤ β ^ 2 := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans ha
  rw [endpoint_difference]
  calc
    ‖(a - 1) * b * (c - 1)‖ ≤ ‖a - 1‖ * ‖b‖ * ‖c - 1‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ β * 1 * β := by gcongr
    _ = β ^ 2 := by ring

lemma abel_first_sum {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (z : 𝕜) (a : ℕ → V) (n : ℕ) :
    (1 - z) • (∑ k ∈ Finset.range n, z ^ k • a k) =
      a 0 - z ^ n • a n + ∑ k ∈ Finset.range n, z ^ (k + 1) • (a (k + 1) - a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, smul_add, ih, Finset.sum_range_succ]
    simp only [pow_succ, mul_smul, sub_smul, smul_sub, one_smul]
    simp only [smul_comm z (z ^ n)]
    abel

lemma abel_second_sum {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (z : 𝕜) (a : ℕ → V) (n : ℕ) :
    (1 - z) ^ 2 • (∑ k ∈ Finset.range n, z ^ k • a k) =
      (1 - z) • a 0 + z • (a 1 - a 0) +
      (∑ k ∈ Finset.range n, z ^ (k + 2) • (a (k + 2) - 2 • a (k + 1) + a k)) -
      (1 - z) • (z ^ n • a n) - z ^ (n + 1) • (a (n + 1) - a n) := by
  have hdiff := abel_first_sum z (fun k => a (k + 1) - a k) n
  rw [pow_two, mul_smul, abel_first_sum]
  have hsum : (∑ k ∈ Finset.range n, z ^ (k + 1) • (a (k + 1) - a k)) =
      z • ∑ k ∈ Finset.range n, z ^ k • (a (k + 1) - a k) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ', mul_smul]
  rw [hsum, smul_add, smul_sub, smul_comm (1 - z) z, hdiff]
  simp only [smul_add, smul_sub, Finset.smul_sum]
  have hsecond : (∑ k ∈ Finset.range n, z • (z ^ (k + 1) •
      (a (k + 1 + 1) - a (k + 1) - (a (k + 1) - a k)))) =
      ∑ k ∈ Finset.range n, z ^ (k + 2) • (a (k + 2) - 2 • a (k + 1) + a k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← mul_smul, ← pow_succ']
    congr 1
    abel
  simp only [smul_sub] at hsecond
  rw [hsecond]
  rw [← mul_smul z (z ^ n), ← pow_succ']
  simp only [smul_sub, smul_add, ← mul_smul, ← pow_succ']
  abel

lemma censored_geometric_telescope {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (q : 𝕜) (f : ℕ → V) (n : ℕ) :
    (1 - q) • (∑ k ∈ Finset.range n, q ^ k • f (k + 1)) + q ^ n • f n =
      f 0 + ∑ k ∈ Finset.range n, q ^ k • (f (k + 1) - f k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ((1 - q) • (∑ k ∈ Finset.range n, q ^ k • f (k + 1)) + q ^ n • f n) +
          q ^ n • (f (n + 1) - f n) := by
        rw [Finset.sum_range_succ, smul_add]
        simp only [pow_succ', mul_smul, sub_smul, one_smul, smul_sub]
        abel
      _ = _ := by rw [ih, Finset.sum_range_succ]; abel

end OracleTemplate.MarkovProduct
