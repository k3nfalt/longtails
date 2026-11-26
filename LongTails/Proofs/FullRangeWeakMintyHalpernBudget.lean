import LongTails.Algorithms.FullRangeWeakMintyHalpern
import Mathlib.Tactic

namespace OracleTemplate.FullRangeWeakMintyHalpern

private lemma calls_per_block {δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) :
    2 * (count δ : ℝ) + 3 ≤ 73 / Real.sqrt δ := by
  have hs := Real.sqrt_pos.2 hd
  have hc : (count δ : ℝ) < 2 + 32 / Real.sqrt δ + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [le_div_iff₀ hs]
  have h := mul_lt_mul_of_pos_right hc hs
  have hcancel : 32 / Real.sqrt δ * Real.sqrt δ = 32 := div_mul_cancel₀ _ hs.ne'
  nlinarith only [h, hcancel, Real.sqrt_le_one.mpr hd1]

lemma value_margin_bound {δ T : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) (hT : 0 ≤ T) :
    ((2 * count δ + 3) * (1 + ⌊256*T/Real.sqrt δ⌋₊) : ℕ) ≤
      73 / Real.sqrt δ + 18688*T/δ := by
  push_cast
  have hf := Nat.floor_le (show 0 ≤ 256*T/Real.sqrt δ by positivity)
  calc
    _ ≤ (73 / Real.sqrt δ) * (1 + 256*T/Real.sqrt δ) := by
      gcongr
      exact calls_per_block hd hd1
    _ = _ := by
      have h := Real.sq_sqrt hd.le
      field_simp
      nlinarith only [congrArg (fun a : ℝ => 18688*T*a) h]

lemma value_lt_hybrid {δ L M ε R : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) (hε : 0 < ε)
    (guard : (2 * (count δ : ℝ) + 3)*256*L^2/(Real.sqrt δ*ε^2) ≤
      (1048576*Real.log (2/δ)/δ^5)*M/ε) :
    (2*count δ+3)*(1+⌊256*L^2*R^2/(Real.sqrt δ*ε^2)⌋₊) <
      ⌈(1048576*Real.log (2/δ)/δ^5)*(1+M*R^2/ε)⌉₊ := by
  let B := 2*(count δ : ℝ)+3
  let H := 1048576*Real.log (2/δ)/δ^5
  have hs := Real.sqrt_pos.2 hd
  have hlog : (1:ℝ)/2 ≤ Real.log (2/δ) := by
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h₂
    exact h₂.trans (Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hd]; linarith))
  have hpow : δ^5 ≤ Real.sqrt δ := by
    have h4 : δ^4 ≤ 1 := pow_le_one₀ hd.le hd1
    have hss := Real.sqrt_le_one.mpr hd1
    nlinarith only [mul_le_mul_of_nonneg_right h4 hd.le, Real.sq_sqrt hd.le,
      mul_le_of_le_one_left hs.le hss]
  have hBH : B < H := by
    apply (calls_per_block hd hd1).trans_lt
    apply (div_lt_div_iff₀ hs (pow_pos hd 5)).2
    nlinarith only [hpow, hs, mul_le_mul_of_nonneg_right hlog hs.le]
  have hf := Nat.floor_le (show 0 ≤ 256*L^2*R^2/(Real.sqrt δ*ε^2) by positivity)
  have hg := mul_le_mul_of_nonneg_right guard (sq_nonneg R)
  change (B*256*L^2/(Real.sqrt δ*ε^2))*R^2 ≤ (H*M/ε)*R^2 at hg
  apply Nat.lt_ceil.mpr
  push_cast
  change B * (1 + _) < H * (1+M*R^2/ε)
  rw [mul_add, mul_one, mul_add, mul_one]
  apply add_lt_add_of_lt_of_le hBH
  calc
    _ ≤ B * (256*L^2*R^2/(Real.sqrt δ*ε^2)) :=
      mul_le_mul_of_nonneg_left hf (by dsimp [B]; positivity)
    _ = B*256*L^2/(Real.sqrt δ*ε^2)*R^2 := by ring
    _ ≤ _ := hg
    _ = _ := by ring

end OracleTemplate.FullRangeWeakMintyHalpern
