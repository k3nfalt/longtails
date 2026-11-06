import LongTails.Proofs.QuasarPowerBarrier
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OracleTemplate.StochasticQuasar

lemma normalized_power_remainder {x : ℝ} (hx : -1 ≤ x) (p : ℕ)
    (hpx : |(p : ℝ) * x| ≤ 1) :
    (1 + x) ^ p ≤ 1 + (p : ℝ) * x + (p : ℝ) ^ 2 * x ^ 2 := by
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) (by simpa only [add_comm] using Real.add_one_le_exp x) p
  rw [← Real.exp_nat_mul] at hh
  have hr := (le_abs_self (Real.exp ((p : ℝ) * x) - 1 - (p : ℝ) * x)).trans
    (Real.abs_exp_sub_one_sub_id_le hpx)
  nlinarith

lemma energy_power_remainder {u j : ℝ} {p : ℕ} (hu : 0 < u) (hp : 2 ≤ p)
    (hj : |j| ≤ u / p) :
    (u + j) ^ p ≤ u ^ p + (p : ℝ) * u ^ (p - 1) * j +
      (p : ℝ) ^ 2 * u ^ (p - 2) * j ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hj1 : |j| ≤ u := hj.trans (div_le_self hu.le hp1)
  have hx : -1 ≤ j / u := by
    apply (le_div_iff₀ hu).mpr
    have hh := neg_abs_le j
    linarith
  have hpx : |(p : ℝ) * (j / u)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hp0, abs_div, abs_of_pos hu]
    have hh := (le_div_iff₀ hp0).mp hj
    rw [← mul_div_assoc, div_le_one hu]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (normalized_power_remainder hx p hpx)
    (pow_nonneg hu.le p)
  have h1 : u ^ p = u ^ (p - 1) * u := by
    rw [← pow_succ]
    congr 1
    omega
  have h2 : u ^ p = u ^ (p - 2) * u ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hleft : u ^ p * (1 + j / u) ^ p = (u + j) ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hleft] at hh
  have he : u ^ p * (1 + (p : ℝ) * (j / u) + (p : ℝ) ^ 2 * (j / u) ^ 2) =
      u ^ p + (p : ℝ) * u ^ (p - 1) * j + (p : ℝ) ^ 2 * u ^ (p - 2) * j ^ 2 := by
    have ht1 : u ^ p * ((p : ℝ) * (j / u)) = (p : ℝ) * u ^ (p - 1) * j := by
      rw [h1]
      field_simp
    have ht2 : u ^ p * ((p : ℝ) ^ 2 * (j / u) ^ 2) =
        (p : ℝ) ^ 2 * u ^ (p - 2) * j ^ 2 := by
      rw [h2]
      field_simp
    rw [mul_add, mul_add, mul_one, ht1, ht2]
  rwa [he] at hh

lemma power_drift_absorption {u B q p D N R d s : ℝ}
    (hB : 0 ≤ B) (hu : B ≤ u) (hq : 0 ≤ q) (hp : 0 ≤ p)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hRN : R ≤ N)
    (hgrad : 18 * p * q ≤ 1 - q) (hnoise : 66 * p * q ≤ 1)
    (hd : d ≤ -(1 - q) * D + N) (hs : s ≤ 18 * q * B * D + 66 * q * B * R) :
    u * d + p * s ≤ 2 * u * N := by
  have hq1 : 0 ≤ 1 - q := (by positivity : 0 ≤ 18 * p * q).trans hgrad
  have hg1 := mul_le_mul_of_nonneg_right hgrad hB
  have hg2 := mul_le_mul_of_nonneg_left hu hq1
  have hg : 18 * p * q * B * D ≤ u * (1 - q) * D :=
    mul_le_mul_of_nonneg_right (by nlinarith) hD
  have hn1 := mul_le_mul_of_nonneg_right hnoise (mul_nonneg hB hR)
  have hn2 := mul_le_mul_of_nonneg_left hRN hB
  have hn3 := mul_le_mul_of_nonneg_right hu (hR.trans hRN)
  have hn : 66 * p * q * B * R ≤ u * N := by nlinarith
  have hd' := mul_le_mul_of_nonneg_left hd (hB.trans hu)
  have hs' := mul_le_mul_of_nonneg_left hs hp
  nlinarith

end OracleTemplate.StochasticQuasar
