import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

omit [Nonempty Ω] in
lemma expect_eq_sum_div (X : Ω → ℝ) : (𝔼 ω, X ω) = (∑ ω, X ω) / Fintype.card Ω := by
  rw [Fintype.expect_eq_sum_div_card]

lemma expect_mul_le_sqrt (X Y : Ω → ℝ) :
    (𝔼 ω, X ω * Y ω) ≤ Real.sqrt (𝔼 ω, X ω ^ 2) * Real.sqrt (𝔼 ω, Y ω ^ 2) := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [expect_eq_sum_div, expect_eq_sum_div, expect_eq_sum_div]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ X Y
  have hX : 0 ≤ ∑ ω, X ω ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : 0 ≤ ∑ ω, Y ω ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_mul (div_nonneg hX hc.le), div_mul_div_comm, ← sq,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc.le]
  apply div_le_div_of_nonneg_right _ hc.le
  have := Real.abs_le_sqrt hcs
  exact (le_abs_self _).trans this

lemma expect_abs_le_sqrt (X : Ω → ℝ) : (𝔼 ω, |X ω|) ≤ Real.sqrt (𝔼 ω, X ω ^ 2) := by
  have h := expect_mul_le_sqrt (fun ω => |X ω|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const, Real.sqrt_one, sq_abs] at h
  exact h

omit [Nonempty Ω] in
lemma expect_indicator_le (q : Ω → ℝ) (hq : ∀ ω, 0 ≤ q ω) {c : ℝ} (hc : 0 < c) :
    (𝔼 ω, if c < q ω then (1 : ℝ) else 0) ≤ (𝔼 ω, q ω) / c := by
  rw [le_div_iff₀ hc, Finset.expect_mul]
  apply Finset.expect_le_expect
  intro ω _
  split_ifs with h
  · linarith
  · simp only [zero_mul]; exact hq ω

lemma expect_sq_indicator_le (X : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    (𝔼 ω, if P ω then X ω ^ 2 else 0) ≤
      Real.sqrt (𝔼 ω, X ω ^ 4) * Real.sqrt (𝔼 ω, if P ω then (1 : ℝ) else 0) := by
  have h := expect_mul_le_sqrt (fun ω => X ω ^ 2) (fun ω => if P ω then (1 : ℝ) else 0)
  have e1 : ∀ ω, X ω ^ 2 * (if P ω then (1 : ℝ) else 0) = if P ω then X ω ^ 2 else 0 := by
    intro ω; split_ifs <;> simp
  have e2 : ∀ ω, (X ω ^ 2) ^ 2 = X ω ^ 4 := fun ω => by ring
  have e3 : ∀ ω, (if P ω then (1 : ℝ) else 0) ^ 2 = if P ω then (1 : ℝ) else 0 := by
    intro ω; split_ifs <;> simp
  simp only [e1, e2, e3] at h
  exact h

omit [Nonempty Ω] in
lemma expect_sq_tail_le (X : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    (𝔼 ω, if t < |X ω| then X ω ^ 2 else 0) ≤ (𝔼 ω, X ω ^ 4) / t ^ 2 := by
  rw [le_div_iff₀ (by positivity), Finset.expect_mul]
  apply Finset.expect_le_expect
  intro ω _
  split_ifs with h
  · have h1 : t ^ 2 ≤ X ω ^ 2 := by
      have := mul_self_le_mul_self ht.le h.le
      rw [← sq, ← sq, sq_abs] at this; exact this
    have : X ω ^ 2 * t ^ 2 ≤ X ω ^ 2 * X ω ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    nlinarith
  · simp only [zero_mul]; positivity

end OracleTemplate.MatrixGeneralizedZO
