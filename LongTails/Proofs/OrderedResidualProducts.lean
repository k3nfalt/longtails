import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.OrderedResidualProducts

lemma prod_le_exp_of_block {ι : Type*} {s t : Finset ι} {a : ι → ℝ} {c : ℝ}
    (hts : t ⊆ s) (ha0 : ∀ j ∈ s, 0 ≤ a j) (ha1 : ∀ j ∈ s, a j ≤ 1)
    (hblock : ∀ j ∈ t, a j ≤ Real.exp (-c)) :
    ∏ j ∈ s, a j ≤ Real.exp (-(t.card : ℝ) * c) := by
  calc
    ∏ j ∈ s, a j ≤ ∏ j ∈ t, a j :=
      Finset.prod_le_prod_of_subset_of_le_one₀ hts ha0 (fun j hj _ => ha1 j hj)
    _ ≤ ∏ _j ∈ t, Real.exp (-c) :=
      Finset.prod_le_prod₀ (fun j hj => ha0 j (hts hj)) hblock
    _ = Real.exp (-(t.card : ℝ) * c) := by
      simp only [Finset.prod_const]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

lemma suffix_prod_le_one {a : ℕ → ℝ} {i T : ℕ}
    (ha : ∀ j < T, 0 ≤ a j)
    (horder : ∀ j k, j < k → k < T → 1 < a k → 1 ≤ a j)
    (hfull : ∏ j ∈ Finset.range T, a j ≤ 1) :
    ∏ j ∈ Finset.Ico i T, a j ≤ 1 := by
  classical
  by_cases hsmall : ∀ j ∈ Finset.Ico i T, a j ≤ 1
  · exact Finset.prod_le_one₀ (fun j hj => ha j (Finset.mem_Ico.mp hj).2) hsmall
  · push Not at hsmall
    obtain ⟨k, hk, hlarge⟩ := hsmall
    apply le_trans _ hfull
    apply Finset.prod_le_prod_of_subset_of_one_le₀
      (fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)
      (fun j hj => ha j (Finset.mem_Ico.mp hj).2)
    intro j hj hji
    have hjT := Finset.mem_range.mp hj
    have hji' : j < i := by
      simp only [Finset.mem_Ico, not_and, not_lt] at hji
      omega
    exact horder j k (lt_of_lt_of_le hji' (Finset.mem_Ico.mp hk).1)
      (Finset.mem_Ico.mp hk).2 hlarge

lemma abs_residual_suffix_le_one {η : ℕ → ℝ} {z : ℝ} {i T : ℕ}
    (hz : 0 ≤ z) (hη : ∀ j < T, 0 ≤ η j)
    (horder : ∀ j k, j < k → k < T → η k ≤ η j)
    (hfull : |∏ j ∈ Finset.range T, (1 - z * η j)| ≤ 1) :
    |∏ j ∈ Finset.Ico i T, (1 - z * η j)| ≤ 1 := by
  simp only [Finset.abs_prod] at hfull ⊢
  refine suffix_prod_le_one (fun j _ => abs_nonneg _) ?_ hfull
  intro j k hjk hk hlarge
  have hηk := hη k hk
  have hmon := mul_le_mul_of_nonneg_left (horder j k hjk hk) hz
  have hprod : 0 ≤ z * η k := mul_nonneg hz hηk
  have htwo : 2 < z * η k := by
    rcases lt_abs.mp hlarge with h | h
    · linarith
    · linarith
  rw [abs_of_nonpos (by linarith : 1 - z * η j ≤ 0)]
  linarith

lemma residual_suffix_gain_sq_le {η : ℕ → ℝ} {z : ℝ} {i T : ℕ}
    (hz : 0 ≤ z) (hη : ∀ j < T, 0 ≤ η j)
    (horder : ∀ j k, j < k → k < T → η k ≤ η j)
    (hfull : |∏ j ∈ Finset.range T, (1 - z * η j)| ≤ 1)
    (hi : i < T) :
    z * η i ^ 2 * (∏ j ∈ Finset.Ico (i + 1) T, (1 - z * η j)) ^ 2 ≤ 2 * η i := by
  let p := ∏ j ∈ Finset.Ico (i + 1) T, (1 - z * η j)
  have hp : |p| ≤ 1 := abs_residual_suffix_le_one hz hη horder hfull
  have hp2 : p ^ 2 ≤ 1 := by
    have := abs_le.mp hp
    nlinarith
  have hηi := hη i hi
  have hzi : 0 ≤ z * η i := mul_nonneg hz hηi
  change z * η i ^ 2 * p ^ 2 ≤ 2 * η i
  by_cases hsmall : z * η i ≤ 2
  · have hmul := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hz (sq_nonneg (η i)))
    have hstep := mul_le_mul_of_nonneg_right hsmall hηi
    nlinarith
  · have hprefix := abs_residual_suffix_le_one (i := i) hz hη horder hfull
    rw [Finset.prod_eq_prod_Ico_succ_bot hi] at hprefix
    change |(1 - z * η i) * p| ≤ 1 at hprefix
    have hprefix2 : ((1 - z * η i) * p) ^ 2 ≤ 1 := by
      have := abs_le.mp hprefix
      nlinarith
    have hpoly : z * η i ≤ 2 * (1 - z * η i) ^ 2 := by
      have : 2 < z * η i := lt_of_not_ge hsmall
      nlinarith [sq_nonneg (z * η i - 2)]
    have hmul := mul_le_mul_of_nonneg_right hpoly (sq_nonneg p)
    have hzpp : z * η i * p ^ 2 ≤ 2 := by
      nlinarith [hprefix2]
    have hfinal := mul_le_mul_of_nonneg_left hzpp hηi
    nlinarith

end OracleTemplate.OrderedResidualProducts
