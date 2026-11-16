import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

namespace LongTails.Proofs.ManyConstraintFinalAlgebra

lemma geom_le {q : ℝ} (hq : 1 < q) (S : ℕ) :
    (∑ i ∈ Finset.range S, q ^ i) ≤ q ^ S / (q - 1) := by
  rw [geom_sum_eq hq.ne', div_le_div_iff_of_pos_right (by linarith)]
  linarith [pow_pos (show (0 : ℝ) < q by linarith) S]

lemma pow_ge {q t X : ℝ} (ht : 0 < t) (hq : 1 + 1 / (12 * t) ≤ q) (hX : 0 < X) {S : ℕ}
    (hS : (12 * t + 1) * Real.log X ≤ S) : X ≤ q ^ S := by
  have hq0 : 0 < q := by have : 0 < 1 / (12 * t) := by positivity
                         linarith
  have h1 : 1 / (12 * t + 1) ≤ Real.log q := by
    have hy : 0 < 1 + 1 / (12 * t) := by positivity
    have := Real.one_sub_inv_le_log_of_pos hy
    have hlog := Real.log_le_log hy hq
    have : 1 - (1 + 1 / (12 * t))⁻¹ = 1 / (12 * t + 1) := by field_simp; ring
    linarith
  have h2 : Real.log X ≤ S * Real.log q := by
    have hpos : (0 : ℝ) < 12 * t + 1 := by positivity
    have : Real.log X ≤ S / (12 * t + 1) := by rw [le_div_iff₀ hpos]; linarith
    calc Real.log X ≤ S / (12 * t + 1) := this
      _ = S * (1 / (12 * t + 1)) := by ring
      _ ≤ S * Real.log q := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg S)
  rw [← Real.log_pow] at h2
  exact (Real.log_le_log_iff hX (pow_pos hq0 S)).mp h2

end LongTails.Proofs.ManyConstraintFinalAlgebra
