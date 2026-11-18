import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.DistributedBudgetPrecision

lemma original_width_le (x : ℝ) :
    Nat.size ⌈1048576 * (1 + x)⌉₊ + 66 ≤ 88 + Nat.size ⌈x⌉₊ := by
  have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil : ⌈1048576 * (1 + x)⌉₊ ≤ 2 ^ 21 * max 1 ⌈x⌉₊ := by
    apply Nat.ceil_le.mpr
    have h1 : (1 : ℝ) ≤ (max 1 ⌈x⌉₊ : ℕ) := by exact_mod_cast le_max_left 1 ⌈x⌉₊
    have h2 : (⌈x⌉₊ : ℝ) ≤ (max 1 ⌈x⌉₊ : ℕ) := by exact_mod_cast le_max_right 1 ⌈x⌉₊
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    norm_num
    norm_num only [Nat.cast_max, Nat.cast_one] at h1 h2
    linarith
  have hpow : max 1 ⌈x⌉₊ < 2 ^ (Nat.size ⌈x⌉₊ + 1) := by
    have hp : 0 < 2 ^ Nat.size ⌈x⌉₊ := by positivity
    have hn := Nat.lt_size_self ⌈x⌉₊
    rw [pow_succ]
    omega
  have hs : Nat.size ⌈1048576 * (1 + x)⌉₊ ≤ 22 + Nat.size ⌈x⌉₊ := by
    apply Nat.size_le.mpr
    calc
      _ ≤ 2 ^ 21 * max 1 ⌈x⌉₊ := hceil
      _ < 2 ^ 21 * 2 ^ (Nat.size ⌈x⌉₊ + 1) := Nat.mul_lt_mul_of_pos_left hpow (by positivity)
      _ = 2 ^ (22 + Nat.size ⌈x⌉₊) := by rw [← pow_add]; congr 1; omega
  omega


lemma size_ceil_le_log (x : ℝ) (hx : 0 ≤ x) :
    (Nat.size ⌈x⌉₊ : ℝ) ≤ 2 * Real.log (1 + x) + 1 := by
  have hl0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  by_cases hn : ⌈x⌉₊ = 0
  · simp only [hn, Nat.size_zero, Nat.cast_zero]
    linarith
  have hs : 1 ≤ Nat.size ⌈x⌉₊ := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  have hp : 2 ^ (Nat.size ⌈x⌉₊ - 1) ≤ ⌈x⌉₊ := Nat.lt_size.mp (by omega)
  have hp' : (2 : ℝ) ^ (Nat.size ⌈x⌉₊ - 1) ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one hx
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (Nat.size ⌈x⌉₊ - 1)) (hp'.trans hc.le)
  rw [Real.log_pow, add_comm x 1] at hl
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    exact ht
  have he : (Nat.size ⌈x⌉₊ : ℝ) = ((Nat.size ⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hs).symm
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (Nat.size ⌈x⌉₊ - 1) : (0 : ℝ) ≤ _)
  nlinarith

lemma log_le_size_ceil (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ (Nat.size ⌈x⌉₊ : ℝ) + 1 := by
  have hp : (⌈x⌉₊ : ℝ) < (2 : ℝ) ^ Nat.size ⌈x⌉₊ := by exact_mod_cast Nat.lt_size_self ⌈x⌉₊
  have hn : (1 : ℕ) ≤ 2 ^ Nat.size ⌈x⌉₊ := Nat.succ_le_of_lt (by positivity)
  have hp1 : (1 : ℝ) ≤ 2 ^ Nat.size ⌈x⌉₊ := by exact_mod_cast hn
  have hb : 1 + x ≤ (2 : ℝ) ^ (Nat.size ⌈x⌉₊ + 1) := by
    rw [pow_succ]
    have hc := Nat.le_ceil x
    linarith
  have hl := Real.log_le_log (by positivity : 0 < 1 + x) hb
  rw [Real.log_pow] at hl
  push_cast at hl
  have htwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hm := mul_le_mul_of_nonneg_left htwo (show 0 ≤ (Nat.size ⌈x⌉₊ : ℝ) + 1 by positivity)
  linarith

lemma width_log_bounds (x : ℝ) (hx : 0 ≤ x) :
    1 + Real.log (1 + x) ≤ (Nat.size ⌈1048576 * (1 + x)⌉₊ + 66 : ℕ) ∧
      (Nat.size ⌈1048576 * (1 + x)⌉₊ + 66 : ℕ) ≤ 128 * (1 + Real.log (1 + x)) := by
  have hl0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hupper := size_ceil_le_log x hx
  have hlower := log_le_size_ceil x hx
  have hc : ⌈x⌉₊ ≤ ⌈1048576 * (1 + x)⌉₊ := Nat.ceil_mono (by linarith)
  have hm : (Nat.size ⌈x⌉₊ : ℝ) ≤ Nat.size ⌈1048576 * (1 + x)⌉₊ := by exact_mod_cast Nat.size_le_size hc
  have hb : (Nat.size ⌈1048576 * (1 + x)⌉₊ + 66 : ℕ) ≤ (88 : ℝ) + Nat.size ⌈x⌉₊ := by
    exact_mod_cast original_width_le x
  push_cast at hb ⊢
  constructor <;> linarith

lemma log_width_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    1 + Real.log (1 + x) ≤ 1 + Real.log (1 + y) := by
  apply add_le_add le_rfl
  exact Real.log_le_log (by positivity) (by linarith)

lemma log_width_polynomial {x y : ℝ} (hx : 1 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 2 * x ^ 5) :
    1 + Real.log (1 + y) ≤ 8 * (1 + Real.log (1 + x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hp := pow_le_pow_left₀ hx0 (show x ≤ 1 + x by linarith) 5
  have hp1 : 1 ≤ (1 + x) ^ 5 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (show 1 ≤ 1 + x by linarith) 5
  have hb : 1 + y ≤ 3 * (1 + x) ^ 5 := by linarith
  have hl := Real.log_le_log (by positivity : 0 < 1 + y) hb
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hthree : Real.log 3 ≤ 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hl0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  linarith

end LongTails.Proofs.DistributedBudgetPrecision
