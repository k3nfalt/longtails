import LongTails.Proofs.GeneralizedMixedRate

open Finset

namespace LongTails.Proofs.NondualMovement

lemma weighted_cube_of_nonneg {ι : Type*} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hxyz : ∀ i ∈ s, z i ^ 3 ≤ x i * y i ^ 2) :
    (∑ i ∈ s, z i) ^ 3 ≤ (∑ i ∈ s, x i) * (∑ i ∈ s, y i) ^ 2 := by
  classical
  let t := s.filter (fun i => 0 < y i)
  have ht : t ⊆ s := filter_subset _ _
  have hzero : ∀ i ∈ s, i ∉ t → z i = 0 := by
    intro i hi hnot
    have hyzero : y i = 0 := by
      have hn : ¬0 < y i := fun hp => hnot (mem_filter.mpr ⟨hi, hp⟩)
      exact le_antisymm (le_of_not_gt hn) (hy i hi)
    have hzpow : z i ^ 3 ≤ (0 : ℝ) ^ 3 := by
      simpa [hyzero] using hxyz i hi
    have hzle := (pow_le_pow_iff_left₀ (hz i hi) (le_refl (0 : ℝ))
      (by decide : 3 ≠ 0)).mp hzpow
    exact le_antisymm hzle (hz i hi)
  have hsum : (∑ i ∈ t, z i) = ∑ i ∈ s, z i := sum_subset ht hzero
  have h := OracleTemplate.GeneralizedAccelerated.weighted_holder_cube t x y z
    (fun i hi => hx i (ht hi)) (fun i hi => (mem_filter.mp hi).2)
    (fun i hi => hz i (ht hi)) (fun i hi => hxyz i (ht hi))
  rw [hsum] at h
  have hxsum := sum_le_sum_of_subset_of_nonneg ht (fun i hi _ => hx i hi)
  have hysum := sum_le_sum_of_subset_of_nonneg ht (fun i hi _ => hy i hi)
  exact h.trans (mul_le_mul hxsum
    (pow_le_pow_left₀ (sum_nonneg (fun i hi => hy i (ht hi))) hysum 2)
    (sq_nonneg _) (sum_nonneg hx))

lemma aggregate_phase_counts {ι : Type*} (s : Finset ι) (Γ M n k : ι → ℝ)
    {c₀ c₁ R : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hΓ : ∀ i ∈ s, 0 < Γ i) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hlow : ∀ i ∈ s, n i ^ 3 * Γ i ≤ c₀ * M i ^ 2)
    (hhigh : ∀ i ∈ s, k i ^ 2 ≤ c₁ * M i)
    (hmovement : (∑ i ∈ s, M i) ≤ R) :
    (∑ i ∈ s, n i) ^ 3 ≤ c₀ * (∑ i ∈ s, 1 / Γ i) * R ^ 2 ∧
      (∑ i ∈ s, k i) ^ 2 ≤ c₁ * s.card * R := by
  constructor
  · have h := weighted_cube_of_nonneg s (fun i => c₀ / Γ i) M n
      (fun i hi => div_nonneg hc₀ (hΓ i hi).le) hM hn (by
        intro i hi
        have hh := (le_div_iff₀ (hΓ i hi)).mpr (hlow i hi)
        simpa only [div_mul_eq_mul_div] using hh)
    have he : (∑ i ∈ s, c₀ / Γ i) = c₀ * ∑ i ∈ s, 1 / Γ i := by
      simp [mul_sum, div_eq_mul_inv]
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sum_nonneg hM) hmovement 2)
      (mul_nonneg hc₀ (sum_nonneg (fun i hi => (one_div_pos.mpr (hΓ i hi)).le))))
  · have hcs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) k
    have hcs' : (∑ i ∈ s, k i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, k i ^ 2 := by
      simpa using hcs
    have hk : (∑ i ∈ s, k i ^ 2) ≤ c₁ * R := by
      calc
        _ ≤ ∑ i ∈ s, c₁ * M i := sum_le_sum hhigh
        _ = c₁ * ∑ i ∈ s, M i := (mul_sum _ _ _).symm
        _ ≤ c₁ * R := mul_le_mul_of_nonneg_left hmovement hc₁
    have hh := hcs'.trans (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _))
    simpa only [mul_left_comm, mul_assoc] using hh

end LongTails.Proofs.NondualMovement
