import Mathlib.Tactic

namespace LongTails.Proofs.TailEntropyBudget

lemma budget_cases (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (N : ℕ)
    (hN : N ≤ ⌊(s + q) / 67108864⌋₊) :
    N = 0 ∨ (8192 ≤ s ∧ N ≤ ⌊s / 16384⌋₊) ∨
      (16777216 ≤ q ∧ N + 1 ≤ ⌊q / 33554432⌋₊ + 1) := by
  by_cases hsq : q ≤ s
  · by_cases hbig : 8192 ≤ s
    · refine Or.inr (Or.inl ⟨hbig, hN.trans (Nat.floor_le_floor ?_)⟩)
      linarith
    · have hf : ⌊(s + q) / 67108864⌋₊ < 1 := by
        apply (Nat.floor_lt (by positivity)).mpr
        norm_num only [Nat.cast_one]
        linarith
      exact Or.inl (by omega)
  · by_cases hbig : 16777216 ≤ q
    · refine Or.inr (Or.inr ⟨hbig, ?_⟩)
      have h := hN.trans (Nat.floor_le_floor (show (s + q) / 67108864 ≤ q / 33554432 by linarith))
      omega
    · have hf : ⌊(s + q) / 67108864⌋₊ < 1 := by
        apply (Nat.floor_lt (by positivity)).mpr
        norm_num only [Nat.cast_one]
        linarith
      exact Or.inl (by omega)

end LongTails.Proofs.TailEntropyBudget
