import Mathlib

namespace LongTails.Proofs.BirchTraceDescent

open Finset

lemma convergence {ι : Type*} (s : Finset ι) (K : ℕ) (owner : ι → ℕ)
    (F G a multiplier N : ℕ → ℝ) (M E b c p q V : ι → ℝ) (C : ι → ι → ℝ)
    (η Δ rate : ℝ) (hη : 0 < η)
    (howner : ∀ e ∈ s, owner e < K)
    (hM : ∀ e ∈ s, 0 ≤ M e)
    (hmult : ∀ k < K, 0 ≤ multiplier k)
    (hcredit : ∀ k < K, rate * G k ≤ (a k + multiplier k) * G k)
    (hweight : ∀ e ∈ s, 0 ≤ c e + multiplier (owner e) * q e)
    (hcolumn : ∀ j ∈ s, (∑ e ∈ s, (c e + multiplier (owner e) * q e) * C e j) ≤
      b j - multiplier (owner j) * p j)
    (hgap : F 0 - F K ≤ Δ)
    (hdescent : ∀ k < K, F (k + 1) - F k ≤ η *
      (N k - a k * G k + ∑ e ∈ s.filter (fun e => owner e = k), (c e * E e - b e * M e)))
    (hcompare : ∀ k < K, G k ≤ ∑ e ∈ s.filter (fun e => owner e = k), (p e * M e + q e * E e))
    (herror : ∀ e ∈ s, E e ≤ (∑ j ∈ s, C e j * M j) + V e) :
    rate * (∑ k ∈ range K, G k) ≤ Δ / η + (∑ k ∈ range K, N k) +
      ∑ e ∈ s, (c e + multiplier (owner e) * q e) * V e := by
  classical
  let w : ι → ℝ := fun e => c e + multiplier (owner e) * q e
  have hpoint (k : ℕ) (hk : k < K) :
      (F (k + 1) - F k) / η + rate * G k ≤
        N k + ∑ e ∈ s.filter (fun e => owner e = k),
          (w e * E e - (b e - multiplier (owner e) * p e) * M e) := by
    have hd := (div_le_iff₀ hη).2 (by simpa only [mul_comm η] using hdescent k hk)
    have hc := mul_le_mul_of_nonneg_left (hcompare k hk) (hmult k hk)
    have hr := hcredit k hk
    rw [mul_sum] at hc
    have heq : (∑ e ∈ s.filter (fun e => owner e = k),
          (w e * E e - (b e - multiplier (owner e) * p e) * M e)) =
        (∑ e ∈ s.filter (fun e => owner e = k), (c e * E e - b e * M e)) +
        ∑ e ∈ s.filter (fun e => owner e = k), multiplier k * (p e * M e + q e * E e) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro e he
      rw [show w e = c e + multiplier k * q e by simp only [w, (mem_filter.mp he).2],
        (mem_filter.mp he).2]
      ring
    rw [heq]
    linarith
  have hs := sum_le_sum (fun k hk => hpoint k (mem_range.mp hk))
  rw [sum_add_distrib, ← sum_div, sum_range_sub, ← mul_sum, sum_add_distrib,
    sum_fiberwise_of_maps_to (fun e he => mem_range.mpr (howner e he))] at hs
  have herr : (∑ e ∈ s, w e * E e) ≤
      (∑ j ∈ s, (b j - multiplier (owner j) * p j) * M j) + ∑ e ∈ s, w e * V e := by
    calc
      _ ≤ ∑ e ∈ s, w e * ((∑ j ∈ s, C e j * M j) + V e) :=
        sum_le_sum (fun e he => mul_le_mul_of_nonneg_left (herror e he) (hweight e he))
      _ = (∑ j ∈ s, (∑ e ∈ s, w e * C e j) * M j) + ∑ e ∈ s, w e * V e := by
        simp_rw [mul_add, sum_add_distrib, mul_sum, ← mul_assoc, sum_mul]
        congr 1
        exact sum_comm
      _ ≤ _ := add_le_add (sum_le_sum (fun j hj =>
        mul_le_mul_of_nonneg_right (hcolumn j hj) (hM j hj))) le_rfl
  rw [sum_sub_distrib] at hs
  have hg := div_le_div_of_nonneg_right hgap hη.le
  rw [show F 0 - F K = -(F K - F 0) by ring, neg_div] at hg
  change rate * (∑ k ∈ range K, G k) ≤ Δ / η + (∑ k ∈ range K, N k) + ∑ e ∈ s, w e * V e
  linarith only [hs, herr, hg]

end LongTails.Proofs.BirchTraceDescent
