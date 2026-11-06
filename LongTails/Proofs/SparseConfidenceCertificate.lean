import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace LongTails.Proofs.SparseConfidenceCertificate

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma certificate_of_upper_risks (q r f u : ι → ℝ) (v F α : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hnormal : ∑ j, q j = 1)
    (hconfidence : ∀ j, u j ≤ f j + 2 * r j)
    (hsaddle : v ≤ ∑ j, q j * u j + α) :
    v - F ≤ 2 * ∑ j, q j * r j - ∑ j, q j * (F - f j) + α := by
  have hupper : ∑ j, q j * u j ≤ ∑ j, q j * (f j + 2 * r j) :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hconfidence j) (hq j))
  have hid : (∑ j, q j * (f j + 2 * r j)) - F =
      2 * ∑ j, q j * r j - ∑ j, q j * (F - f j) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [← mul_assoc, mul_comm (q _) 2, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hnormal]
    ring
  linarith

lemma selected_gap_bound (q r Δ : ι → ℝ) (S : Finset ι) (i : ι) (E : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hΔ : ∀ j, 0 ≤ Δ j)
    (hi : 0 < q i) (hsupport : ∀ j, j ∉ S → q j = 0)
    (hmax : ∀ j ∈ S, q j * r j ≤ q i * r i)
    (hcertificate : ∑ j, q j * Δ j ≤ 2 * ∑ j, q j * r j + E)
    (herror : E ≤ q i * r i) :
    Δ i ≤ (2 * (S.card : ℝ) + 1) * r i := by
  have hsingle : q i * Δ i ≤ ∑ j, q j * Δ j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hq j) (hΔ j)) (Finset.mem_univ i)
  have hsum : ∑ j, q j * r j = ∑ j ∈ S, q j * r j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    simp [hsupport j hj]
  have hbound : ∑ j ∈ S, q j * r j ≤ (S.card : ℝ) * (q i * r i) := by
    calc
      _ ≤ ∑ _j ∈ S, q i * r i := Finset.sum_le_sum hmax
      _ = _ := by simp [nsmul_eq_mul]
  have hmul : q i * Δ i ≤ q i * ((2 * (S.card : ℝ) + 1) * r i) := by
    rw [hsum] at hcertificate
    nlinarith
  exact (mul_le_mul_iff_right₀ hi).mp hmul

lemma output_gap_bound (q r Δ : ι → ℝ) (S : Finset ι) (M ε gap E : ℝ)
    (hΔ : ∀ j, 0 ≤ Δ j) (hq : ∀ j, 0 ≤ q j)
    (hsupport : ∀ j, j ∉ S → q j = 0)
    (hmax : ∀ j ∈ S, q j * r j ≤ M)
    (hbudget : 2 * (S.card : ℝ) * M + E ≤ ε)
    (hcertificate : gap ≤ 2 * ∑ j, q j * r j - ∑ j, q j * Δ j + E) :
    gap ≤ ε := by
  have hsum : ∑ j, q j * r j = ∑ j ∈ S, q j * r j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    simp [hsupport j hj]
  have hbound : ∑ j ∈ S, q j * r j ≤ (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ _j ∈ S, M := Finset.sum_le_sum hmax
      _ = _ := by simp [nsmul_eq_mul]
  have hnonneg : 0 ≤ ∑ j, q j * Δ j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hq j) (hΔ j))
  rw [hsum] at hcertificate
  linarith

end LongTails.Proofs.SparseConfidenceCertificate
