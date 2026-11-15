import LongTails.Proofs.InterpolatedFiniteSumLinkParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.InterpolatedFiniteSumLinkLength

lemma scale_identity (q : ℝ) (hq : 0 ≤ q) :
    let t := (q / 64) ^ (2 / 3 : ℝ)
    q = 64 * t * Real.sqrt t := by
  dsimp only
  by_cases hz : q = 0
  · subst q; norm_num
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ q / 64)]
  rw [mul_assoc, ← Real.rpow_add (by positivity : 0 < q / 64)]
  norm_num
  ring

lemma length_bounds (t : ℝ) (ht : 1 ≤ t) :
    0 < ⌈t⌉₊ ∧ t ≤ (⌈t⌉₊ : ℝ) ∧ (⌈t⌉₊ : ℝ) ≤ 2 * t := by
  have hp : 0 < t := by linarith
  exact ⟨Nat.ceil_pos.mpr hp, Nat.le_ceil t, by have := Nat.ceil_lt_add_one hp.le; linarith⟩

lemma shape_conditions (q t η : ℝ) (ht : 1 ≤ t) (_hη : 0 ≤ η)
    (heta : η ≤ t / 8) (hid : q = 64 * t * Real.sqrt t) :
    128 * η * Real.sqrt (⌈t⌉₊ : ℝ) ≤ q ∧
    2 * (1 + η) * Real.sqrt (⌈t⌉₊ : ℝ) ≤ q ∧
    q ≤ 64 * (⌈t⌉₊ : ℝ) * Real.sqrt (⌈t⌉₊ : ℝ) ∧ (⌈t⌉₊ : ℝ) ≤ q := by
  obtain ⟨hT, htT, hTt⟩ := length_bounds t ht
  have ht0 : 0 ≤ t := by linarith
  have hs := Real.sq_sqrt ht0
  have hST := Real.sq_sqrt (Nat.cast_nonneg ⌈t⌉₊)
  have hs0 := Real.sqrt_nonneg t
  have hST0 := Real.sqrt_nonneg (⌈t⌉₊ : ℝ)
  have hs1 : 1 ≤ Real.sqrt t := by simpa using Real.sqrt_le_sqrt ht
  have hsupper : Real.sqrt (⌈t⌉₊ : ℝ) ≤ 2 * Real.sqrt t := by nlinarith
  have hslower := Real.sqrt_le_sqrt htT
  have h1 := mul_le_mul heta hsupper hST0 (by positivity : 0 ≤ t / 8)
  have h2 := mul_le_mul (show 1 + η ≤ 2 * t by linarith) hsupper hST0 (by positivity : 0 ≤ 2 * t)
  have h3 := mul_le_mul htT hslower hs0 (Nat.cast_nonneg ⌈t⌉₊ : (0 : ℝ) ≤ _)
  have h4 := mul_le_mul_of_nonneg_left hs1 ht0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith only [h1, h2, h3, h4, hid, ht0, hs0, hTt]

lemma scale_power (q : ℝ) (hq : 0 ≤ q) :
    q ^ (2 / 3 : ℝ) = 16 * (q / 64) ^ (2 / 3 : ℝ) := by
  have hc : (64 : ℝ) ^ (2 / 3 : ℝ) = 16 := by
    rw [show (64 : ℝ) = 4 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [Real.div_rpow hq (by norm_num), hc]
  ring

lemma scale_ge_one (q : ℝ) (hq : 64 ≤ q) : 1 ≤ (q / 64) ^ (2 / 3 : ℝ) := by
  have hh : (1 : ℝ) ≤ q / 64 := by linarith
  simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hh (by norm_num : (0 : ℝ) ≤ 2 / 3)

end LongTails.Proofs.InterpolatedFiniteSumLinkLength
