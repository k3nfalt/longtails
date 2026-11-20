import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.GraceBatchAllocation

lemma batch_capacity {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (h : ι → ℝ) (hh : ∀ i ∈ s, 0 < h i) (B : ℕ) :
    let T := (B + (s.card : ℝ)) / ∑ i ∈ s, (h i)⁻¹
    B ≤ ∑ i ∈ s, ⌊T / h i⌋₊ := by
  intro T
  have hsum : 0 < ∑ i ∈ s, (h i)⁻¹ :=
    Finset.sum_pos (fun i hi => inv_pos.mpr (hh i hi)) hs
  have htotal : ∑ i ∈ s, T / h i = B + (s.card : ℝ) := by
    simp only [div_eq_mul_inv, ← Finset.mul_sum]
    exact div_mul_cancel₀ _ hsum.ne'
  have hfloor := Finset.sum_le_sum (s := s) (f := fun i => T / h i)
    (g := fun i => (⌊T / h i⌋₊ : ℝ) + 1) fun i _ => (Nat.lt_floor_add_one _).le
  rw [htotal, Finset.sum_add_distrib] at hfloor
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hfloor
  exact_mod_cast (le_of_add_le_add_right hfloor)

lemma trim_batch {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℕ)
    (B : ℕ) (hB : B ≤ ∑ i ∈ s, c i) :
    ∃ a : ι → ℕ, (∀ i, a i ≤ c i) ∧ (∀ i ∉ s, a i = 0) ∧ ∑ i ∈ s, a i = B := by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    simp at hB
    exact ⟨fun _ => 0, by simp, by simp, by simp [hB]⟩
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj] at hB
    obtain ⟨a, ha, hout, hsum⟩ := ih (B - c j) (by omega)
    refine ⟨Function.update a j (min B (c j)), ?_, ?_, ?_⟩
    · intro i
      by_cases he : i = j
      · subst i
        simp
      · simpa [Function.update_of_ne he] using ha i
    · intro i hi
      have he : i ≠ j := fun hij => hi (hij ▸ Finset.mem_insert_self j s)
      exact (Function.update_of_ne he ..).trans (hout i (fun h => hi (Finset.mem_insert_of_mem h)))
    · rw [Finset.sum_insert hj, Function.update_self]
      have he : ∑ i ∈ s, Function.update a j (min B (c j)) i = ∑ i ∈ s, a i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ j := fun e => hj (e ▸ hi)
        exact Function.update_of_ne hne ..
      rw [he, hsum]
      omega

end LongTails.Proofs.GraceBatchAllocation
