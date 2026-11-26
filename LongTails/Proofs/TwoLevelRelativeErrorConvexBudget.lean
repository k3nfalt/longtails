import LongTails.Algorithms.TwoLevelRelativeErrorConvex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace LongTails.Proofs.TwoLevelRelativeErrorConvex
open LongTails.Algorithms.TwoLevelRelativeErrorConvex

lemma inner_cost {α : ℝ} (ha : 0 < α) (hb : α ≤ 1/32) :
    (innerCount α : ℝ) ≤ 1711 * (1/α)^2 * Real.log (1/α) := by
  let t := 1/α
  have ht : (32:ℝ) ≤ t := by dsimp [t]; rw [le_div_iff₀ ha]; linarith
  have ht1 : 1 ≤ t := by linarith
  have ht2 : 1 ≤ t^2 := one_le_pow₀ ht1
  have ht4 : 2 ≤ t^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) ht 4]
  have hat : α^2*t^2 = 1 := by dsimp [t]; field_simp
  let r := (1+t^4)/(1-2*α)
  have hd : 0 < 1-2*α := by linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr : r ≤ 2*t^4 := by
    dsimp [r]; rw [div_le_iff₀ hd]
    nlinarith only [ht4, mul_nonneg (show 0 ≤ 1/32-α by linarith) (sq_nonneg (t^2))]
  have hs : Real.sqrt r ≤ 2*t^2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr; nlinarith only [hr, sq_nonneg (t^2)]
  have hH : 8*Real.sqrt r+128*α^2*r ≤ 272*t^2 := by
    nlinarith only [hs,mul_le_mul_of_nonneg_left hr (sq_nonneg α),
      congrArg (fun x : ℝ => x*t^2) hat]
  let b := (1+t^4)/(32*α^2)
  have hlog : Real.log b ≤ 6*Real.log t := by
    have he : b = (1+t^4)*t^2/32 := by dsimp [b,t]; field_simp
    have hh : b ≤ t^6 := by rw [he]; nlinarith only [mul_le_mul_of_nonneg_right ht4 (sq_nonneg t)]
    simpa [Real.log_pow] using Real.log_le_log (show 0 < b by dsimp [b]; positivity) hh
  have hlog1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hceil : (innerCount α : ℝ) < (8*Real.sqrt r+128*α^2*r)*Real.log b + 1 := by
    have ht4' : 1/α^4 = t^4 := by simp [t]
    have hb1 : 1 ≤ b := by dsimp [b]; rw [le_div_iff₀ (by positivity)]; nlinarith
    simpa only [innerCount,ht4'] using Nat.ceil_lt_add_one
      (mul_nonneg (by positivity : 0 ≤ 8*Real.sqrt r+128*α^2*r) (Real.log_nonneg hb1))
  have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 8*Real.sqrt r+128*α^2*r)
  have hh' := mul_le_mul_of_nonneg_right hH (by positivity : 0 ≤ 6*Real.log t)
  change _ ≤ 1711*t^2*Real.log t
  nlinarith only [hceil,hh,hh',mul_le_mul ht2 hlog1 (by norm_num) (by positivity)]

lemma oracle_cost {α T : ℝ} (ha : 0 < α) (hb : α ≤ 1/32) (hT : 1 ≤ T) :
    (horizon α T * innerCount α : ℕ) ≤
      1711 * ((1/α)^2 + Real.sqrt (12*Real.exp 1)*Real.sqrt T + 1536*Real.exp 1*α^4*T)
        * Real.log (1/α) := by
  have hT0 : 0 ≤ T := by linarith
  have hc := inner_cost ha hb
  have hk := Nat.ceil_lt_add_one (by positivity :
    0 ≤ Real.sqrt (12*Real.exp 1*α^4*T)+1536*Real.exp 1*α^6*T)
  change (horizon α T : ℝ) < _ at hk
  have hs : Real.sqrt (12*Real.exp 1*α^4*T) = Real.sqrt (12*Real.exp 1)*α^2*Real.sqrt T := by
    rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity),
      show α^4 = (α^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [hs] at hk
  have hh := mul_le_mul hk.le hc (Nat.cast_nonneg _) (by positivity)
  push_cast
  apply hh.trans
  apply le_of_eq
  field_simp
  ring

end LongTails.Proofs.TwoLevelRelativeErrorConvex
