import LongTails.Proofs.LocalizedMonotoneParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.LocalizedMonotoneBudget

lemma floor_power_bound (q : ℝ) (hq : 1 ≤ q) :
    ((⌊q ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2) ^ 2 *
      Real.sqrt ((⌊q ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2) ≤ 16 * q := by
  let s := q ^ (2 / 5 : ℝ)
  let m := (⌊s⌋₊ : ℝ) + 2
  have hq0 : 0 ≤ q := by linarith
  have hs : 1 ≤ s := by
    dsimp [s]
    exact Real.one_le_rpow hq (by norm_num)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hms : m ≤ 3 * s := by
    have hf := Nat.floor_le (show 0 ≤ s by linarith)
    dsimp [m]
    linarith
  have hs5 : s ^ 5 = q ^ 2 := by
    dsimp [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
    norm_num
  have hm5 := pow_le_pow_left₀ hm hms 5
  rw [mul_pow, hs5] at hm5
  have hsq : (m ^ 2 * Real.sqrt m) ^ 2 = m ^ 5 := by
    rw [mul_pow, Real.sq_sqrt hm]
    ring
  change m ^ 2 * Real.sqrt m ≤ 16 * q
  nlinarith [sq_nonneg q, Real.sqrt_nonneg m]

lemma floor_budget_residual (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hregime : 4096 * ε ≤ L * R ^ 2) :
    2 * ε < L * R ^ 2 /
      (32 * ((⌊(L * R ^ 2 / (4096 * ε)) ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2) ^ 2 *
        Real.sqrt ((⌊(L * R ^ 2 / (4096 * ε)) ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2)) := by
  let q := L * R ^ 2 / (4096 * ε)
  have hq : 1 ≤ q := by
    apply (le_div_iff₀ (by positivity : 0 < 4096 * ε)).mpr
    simpa using hregime
  have hb := floor_power_bound q hq
  have hm : 0 < (⌊q ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2 := by positivity
  change 2 * ε < L * R ^ 2 /
    (32 * ((⌊q ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2) ^ 2 * Real.sqrt ((⌊q ^ (2 / 5 : ℝ)⌋₊ : ℝ) + 2))
  apply (lt_div_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 64 * ε by positivity)
  have he : 4096 * ε * q = L * R ^ 2 := by dsimp [q]; field_simp
  have hp : 0 < L * R ^ 2 := by positivity
  nlinarith

end LongTails.Proofs.LocalizedMonotoneBudget
