import LongTails.Proofs.DistributedBudgetPrecision
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Proofs.DistributedBudgetWidths

lemma argument_bounds {A R d n : ℝ} (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hnd : n ≤ d ^ 3) :
    1 ≤ A * Real.sqrt d ∧
      A * Real.sqrt d ≤ (d ^ 2 * A + d * min R n) / Real.sqrt n ∧
      (d ^ 2 * A + d * min R n) / Real.sqrt n ≤ 2 * (A * Real.sqrt d) ^ 5 := by
  have hA0 : 0 ≤ A := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hn0 : 0 < n := by linarith
  have hs0 := Real.sqrt_nonneg d
  have hs2 := Real.sq_sqrt hd0
  have hz0 := Real.sqrt_pos.2 hn0
  have hz2 := Real.sq_sqrt hn0.le
  have hs1 : 1 ≤ Real.sqrt d := by nlinarith
  have hz1 : 1 ≤ Real.sqrt n := by nlinarith [Real.sqrt_nonneg n]
  have hmin : 0 ≤ min R n := le_min hR hn0.le
  have hzbound : Real.sqrt n ≤ d * Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hs2]
    nlinarith
  have hxs : 1 ≤ A * Real.sqrt d := by nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hs0]
  refine ⟨hxs, ?_, ?_⟩
  · apply (le_div_iff₀ hz0).mpr
    have hm := mul_le_mul_of_nonneg_left hzbound (show 0 ≤ A * Real.sqrt d by positivity)
    have he : A * Real.sqrt d * (d * Real.sqrt d) = d ^ 2 * A := by
      calc
        _ = A * d * (Real.sqrt d) ^ 2 := by ring
        _ = _ := by rw [hs2]; ring
    rw [he] at hm
    nlinarith [mul_nonneg hd0 hmin]
  · have hu : (d ^ 2 * A + d * min R n) / Real.sqrt n ≤ d ^ 2 * A + d * Real.sqrt n := by
      apply (div_le_iff₀ hz0).mpr
      have hm := mul_le_mul_of_nonneg_left (min_le_right R n) hd0
      have ha := mul_nonneg (show 0 ≤ d ^ 2 * A by positivity) (show 0 ≤ Real.sqrt n - 1 by linarith)
      nlinarith
    have hA4 : 1 ≤ A ^ 4 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA 4
    have hA5 : A ≤ A ^ 5 := by nlinarith [mul_nonneg hA0 (show 0 ≤ A ^ 4 - 1 by linarith)]
    have hs45 : (Real.sqrt d) ^ 4 ≤ (Real.sqrt d) ^ 5 := by
      nlinarith [mul_nonneg (show 0 ≤ (Real.sqrt d) ^ 4 by positivity) (show 0 ≤ Real.sqrt d - 1 by linarith)]
    have hterm1 : d ^ 2 * A ≤ (A * Real.sqrt d) ^ 5 := by
      calc
        _ = A * (Real.sqrt d) ^ 4 := by
          calc
            _ = ((Real.sqrt d) ^ 2) ^ 2 * A := by rw [hs2]
            _ = _ := by ring
        _ ≤ A ^ 5 * (Real.sqrt d) ^ 5 := mul_le_mul hA5 hs45 (by positivity) (by positivity)
        _ = _ := by ring
    have hterm2 : d * Real.sqrt n ≤ (A * Real.sqrt d) ^ 5 := by
      calc
        _ ≤ d * (d * Real.sqrt d) := mul_le_mul_of_nonneg_left hzbound hd0
        _ = (Real.sqrt d) ^ 5 := by
          calc
            _ = (Real.sqrt d) ^ 2 * ((Real.sqrt d) ^ 2 * Real.sqrt d) := by rw [hs2]
            _ = _ := by ring
        _ ≤ A ^ 5 * (Real.sqrt d) ^ 5 := by
          have hA51 : 1 ≤ A ^ 5 := hA.trans hA5
          nlinarith [mul_nonneg (show 0 ≤ A ^ 5 - 1 by linarith) (show 0 ≤ (Real.sqrt d) ^ 5 by positivity)]
        _ = _ := by ring
    linarith


lemma width_comparison {A R d n : ℝ} (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hnd : n ≤ d ^ 3) :
    1 + Real.log (1 + A * Real.sqrt d) ≤
      1 + Real.log (1 + (d ^ 2 * A + d * min R n) / Real.sqrt n) ∧
    1 + Real.log (1 + (d ^ 2 * A + d * min R n) / Real.sqrt n) ≤
      8 * (1 + Real.log (1 + A * Real.sqrt d)) := by
  obtain ⟨hx, hxy, hy⟩ := argument_bounds hA hR hd hn hnd
  have hx0 : 0 ≤ A * Real.sqrt d := by linarith
  exact ⟨DistributedBudgetPrecision.log_width_mono hx0 hxy,
    DistributedBudgetPrecision.log_width_polynomial hx (hx0.trans hxy) hy⟩

end LongTails.Proofs.DistributedBudgetWidths
