import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace LongTails.Proofs.EscapeChainGaps

def gap (τ : ℕ → ℕ) : ℕ → ℕ
  | 0 => τ 0
  | j + 1 => τ (j + 1) - τ j

lemma gap_sum (τ : ℕ → ℕ) (hinc : ∀ j, τ j ≤ τ (j + 1)) (K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), gap τ j = τ K := by
  induction K with
  | zero => simp [gap]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [gap]
    have := hinc K
    omega

theorem many_small_gaps {K N m : ℕ} (τ : ℕ → ℕ) (hK : 0 < K)
    (hinc : ∀ j, j + 1 < K → τ j < τ (j + 1)) (hlast : τ (K - 1) < N) (hm : 2 * N ≤ (m + 1) * K) :
    K < 2 * ((Finset.range K).filter (fun j => gap τ j ≤ m)).card := by
  classical
  set τ' : ℕ → ℕ := fun j => if j < K then τ j else τ (K - 1) + j with hτ'
  have hinc' : ∀ j, τ' j ≤ τ' (j + 1) := by
    intro j
    simp only [hτ']
    by_cases h1 : j + 1 < K
    · rw [ite_eq_left (by omega), ite_eq_left h1]; exact (hinc j h1).le
    · by_cases h2 : j < K
      · rw [ite_eq_left h2, ite_eq_right h1]
        have : j = K - 1 := by omega
        subst this; omega
      · rw [ite_eq_right h2, ite_eq_right h1]; omega
  have hgap : ∀ j < K, gap τ' j = gap τ j := by
    intro j hj
    cases j with
    | zero => simp [gap, hτ', hK]
    | succ j => simp [gap, hτ', hj, show j < K by omega]
  have hsum := gap_sum τ' hinc' (K - 1)
  rw [show K - 1 + 1 = K by omega] at hsum
  have hsum' : ∑ j ∈ Finset.range K, gap τ j = τ (K - 1) := by
    rw [← Finset.sum_congr rfl fun j hj => hgap j (Finset.mem_range.1 hj), hsum]
    simp [hτ', show K - 1 < K by omega]
  set G := (Finset.range K).filter (fun j => gap τ j ≤ m)
  set B := (Finset.range K).filter (fun j => ¬ gap τ j ≤ m)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun j => gap τ j ≤ m)
    (gap τ)
  have hB : B.card * (m + 1) ≤ ∑ j ∈ B, gap τ j := by
    have := Finset.card_nsmul_le_sum B (gap τ) (m + 1) (fun j hj => by
      have := (Finset.mem_filter.1 hj).2; omega)
    simpa using this
  have hcard : G.card + B.card = K := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range K)
      (fun j => gap τ j ≤ m)
    rw [Finset.card_range] at this
    exact this
  have hBsum : ∑ j ∈ B, gap τ j < N := by
    have : ∑ j ∈ B, gap τ j ≤ ∑ j ∈ Finset.range K, gap τ j := by
      rw [← hsplit]; exact Nat.le_add_left _ _
    omega
  have h1 : 2 * (B.card * (m + 1)) < (m + 1) * K := by
    calc 2 * (B.card * (m + 1)) < 2 * N := by omega
      _ ≤ (m + 1) * K := hm
  have h2 : 2 * B.card < K := by
    by_contra h
    push Not at h
    have : (m + 1) * K ≤ (m + 1) * (2 * B.card) := Nat.mul_le_mul_left _ h
    nlinarith
  omega

end LongTails.Proofs.EscapeChainGaps
