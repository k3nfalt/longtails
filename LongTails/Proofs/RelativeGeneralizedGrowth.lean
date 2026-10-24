import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OracleTemplate.RelativeGeneralized

lemma weight_growth {A Q L : ℝ} (hA : 0 < A) (hQ : 1 ≤ Q) (hL : 0 < L) :
    let a := A / (4096 * (Q + Real.sqrt (L * A)))
    let s := Real.sqrt (L * A)
    let t := Real.sqrt (L * (A + a))
    1 / 12288 ≤ (t + 2 * Q * Real.log t) - (s + 2 * Q * Real.log s) := by
  let s := Real.sqrt (L * A)
  let a := A / (4096 * (Q + s))
  let t := Real.sqrt (L * (A + a))
  change 1 / 12288 ≤ (t + 2 * Q * Real.log t) - (s + 2 * Q * Real.log s)
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : 0 < Q + s := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have heq : a * (4096 * (Q + s)) = A := by dsimp [a]; field_simp
  have hss : s ^ 2 = L * A := Real.sq_sqrt (by positivity)
  have htt : t ^ 2 = L * (A + a) := Real.sq_sqrt (by positivity)
  have haA : a ≤ A := by nlinarith [mul_pos ha hs]
  have hst : s ≤ t := by nlinarith
  have hts : t ≤ 2 * s := by nlinarith [mul_le_mul_of_nonneg_left haA hL.le]
  have hdiff : (t - s) * (Q + s) ≥ s / 12288 := by
    have hid : (t - s) * (t + s) * (Q + s) = s ^ 2 / 4096 := by
      have hh := congrArg (fun r : ℝ => L * r) heq
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hts
      (mul_nonneg (sub_nonneg.mpr hst) hq.le)
    nlinarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hs ht)
  rw [Real.log_div hs.ne' ht.ne'] at hl
  have hlog : t - s ≤ t * (Real.log t - Real.log s) := by
    have hh := mul_le_mul_of_nonneg_left hl ht.le
    have he : t * (s / t - 1) = s - t := by field_simp
    nlinarith
  have hlog0 : 0 ≤ Real.log t - Real.log s := sub_nonneg.mpr (Real.log_le_log hs hst)
  have hlog2 : t - s ≤ 2 * s * (Real.log t - Real.log s) :=
    hlog.trans (mul_le_mul_of_nonneg_right hts hlog0)
  have hscale := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ Q by linarith)
  nlinarith

end OracleTemplate.RelativeGeneralized
