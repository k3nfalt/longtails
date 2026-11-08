import LongTails.Proofs.BirchCollectionWeights

namespace LongTails.Proofs.BirchCollectionPolicies

open Finset

lemma one_sub_sum_le_product {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai := ha i (mem_insert_self _ _)
      have hai1 := ha1 i (mem_insert_self _ _)
      have hsum : 0 ≤ ∑ j ∈ s, a j := sum_nonneg (fun j hj => ha j (mem_insert_of_mem hj))
      have hh := ih (fun j hj => ha j (mem_insert_of_mem hj))
        (fun j hj => ha1 j (mem_insert_of_mem hj))
      have hmul := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hai1)
      rw [sum_insert hi, prod_insert hi]
      nlinarith [mul_nonneg hai hsum]

lemma work_counter_gate {ι : Type*} (s : Finset ι) (β : ι → ℝ)
    (hβ : ∀ i ∈ s, 0 ≤ β i) (hcap : ∀ i ∈ s, β i ≤ 1 / 2)
    (hwork : (∑ i ∈ s, β i) ≤ 1 / 4) :
    1 ≤ 2 * ∏ i ∈ s, (1 - 2 * β i) := by
  have hh := one_sub_sum_le_product s (fun i => 2 * β i)
    (fun i hi => mul_nonneg (by norm_num) (hβ i hi))
    (fun i hi => by linarith [hcap i hi])
  rw [← mul_sum] at hh
  linarith

lemma quota_overshoot (B before last : ℕ) (hbefore : before < B) (hlast : last ≤ B)
    (hstop : B ≤ before + last) : B ≤ before + last ∧ before + last < 2 * B := by omega

lemma variable_collection_parameters (B b : ℕ) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B) :
    let β := (b : ℝ) / (8 * B)
    0 < β ∧ β ≤ 1 / 8 ∧ β * B ≤ b ∧ (B : ℝ) * 8 * β = b := by
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hbBR : (b : ℝ) ≤ B := Nat.cast_le.mpr hbB
  dsimp only
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    nlinarith
  · have he : (b : ℝ) / (8 * B) * B = b / 8 := by field_simp
    rw [he]
    linarith
  · field_simp

lemma variable_phase_mass {ι : Type*} (s : Finset ι) (b : ι → ℕ) (B : ℕ)
    (hB : 0 < B) (hlo : B ≤ ∑ i ∈ s, b i) (hhi : (∑ i ∈ s, b i) < 2 * B) :
    1 / 8 ≤ ∑ i ∈ s, (b i : ℝ) / (8 * B) ∧
      (∑ i ∈ s, (b i : ℝ) / (8 * B)) < 1 / 4 := by
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hloR : (B : ℝ) ≤ ∑ i ∈ s, (b i : ℝ) := by exact_mod_cast hlo
  have hhiR : (∑ i ∈ s, (b i : ℝ)) < 2 * B := by exact_mod_cast hhi
  rw [← sum_div]
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    nlinarith

lemma variable_phase_gate {ι : Type*} (s : Finset ι) (b : ι → ℕ) (B : ℕ)
    (hB : 0 < B) (hb : ∀ i ∈ s, b i ≤ B)
    (hwork : (∑ i ∈ s, b i) ≤ 2 * B) :
    1 ≤ 2 * ∏ i ∈ s, (1 - 2 * ((b i : ℝ) / (8 * B))) := by
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  apply work_counter_gate
  · intro i _
    positivity
  · intro i hi
    have hiR : (b i : ℝ) ≤ B := Nat.cast_le.mpr (hb i hi)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    linarith
  · have hworkR : (∑ i ∈ s, (b i : ℝ)) ≤ 2 * B := by exact_mod_cast hwork
    rw [← sum_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    nlinarith

end LongTails.Proofs.BirchCollectionPolicies
