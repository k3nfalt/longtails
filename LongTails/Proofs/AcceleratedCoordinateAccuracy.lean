import LongTails.Proofs.AcceleratedCoordinateConvergence
import Mathlib.Data.Nat.Log

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

lemma contraction_block (p : Params) (hμ : 0 < p.μ) :
    (1 - tau p) ^ (2 * totalWeight p) ≤ (1 / 2 : ℝ) := by
  have hM : (1 : ℝ) ≤ totalWeight p := by exact_mod_cast totalWeight_pos p
  have hD : 0 < 2 * (totalWeight p : ℝ) - 1 := by linarith
  have hq : 0 ≤ 1 - tau p := (sub_pos.mpr (tuning p hμ).2.1).le
  let a := 1 / (2 * (totalWeight p : ℝ) - 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h := one_add_mul_le_pow (show -2 ≤ a by linarith) (2 * totalWeight p)
  have hone : 1 ≤ ((2 * totalWeight p : ℕ) : ℝ) * a := by
    dsimp [a]
    push_cast
    rw [mul_one_div]
    apply (le_div_iff₀ hD).mpr
    linarith
  have hp : 2 ≤ (1 + a) ^ (2 * totalWeight p) := by linarith
  have hid : (1 - tau p) * (1 + a) = 1 := by
    dsimp [tau, a]
    have hM0 : (totalWeight p : ℝ) ≠ 0 := by exact_mod_cast (totalWeight_pos p).ne'
    field_simp
    ring
  have hid' : (1 - tau p) ^ (2 * totalWeight p) * (1 + a) ^ (2 * totalWeight p) = 1 := by
    rw [← mul_pow, hid, one_pow]
  have hh := mul_le_mul_of_nonneg_left hp (pow_nonneg hq (2 * totalWeight p))
  nlinarith only [hh, hid']

lemma coordinate_budget_accuracy (p : Params) (hμ : 0 < p.μ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    let B := Nat.clog 2 ⌈2 * p.Δ / p.ε⌉₊
    (1 - tau p) ^ (2 * totalWeight p * B) * (2 * p.Δ) ≤ p.ε := by
  let B := Nat.clog 2 ⌈2 * p.Δ / p.ε⌉₊
  have hq : 0 ≤ 1 - tau p := (sub_pos.mpr (tuning p hμ).2.1).le
  have hp : (1 - tau p) ^ (2 * totalWeight p * B) ≤ (1 / 2 : ℝ) ^ B := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hq _) (contraction_block p hμ) B
  have hc : 2 * p.Δ / p.ε ≤ (2 : ℝ) ^ B := by
    calc
      _ ≤ (⌈2 * p.Δ / p.ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ B : ℕ) : ℝ) := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈2 * p.Δ / p.ε⌉₊
      _ = _ := by norm_cast
  have hs : 2 * p.Δ / (2 : ℝ) ^ B ≤ p.ε := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ B)).mpr
    have h := (div_le_iff₀ hε).mp hc
    nlinarith only [h]
  have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 2 * p.Δ)
  dsimp only
  exact hh.trans (by simpa [div_pow, div_eq_mul_inv, mul_comm] using hs)

end OracleTemplate.AcceleratedCoordinate
