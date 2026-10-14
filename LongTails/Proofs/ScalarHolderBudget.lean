import LongTails.Proofs.ScalarHolderSearch
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory Classical

namespace OracleTemplate.ScalarHolderSearch

lemma noise_exponent_ge_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) : 2 ≤ p / (p - 1) := by
  apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
  linarith

lemma scaled_noise_power {r p a : ℝ} (hr : 0 ≤ r) (hp : 1 < p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (ha128 : a ≤ 128) :
    (a * r) ^ (p / (p - 1)) ≤ (2 : ℝ) ^ (14 / (p - 1)) * r ^ (p / (p - 1)) := by
  have hd : 0 < p - 1 := by linarith
  have hq : 0 ≤ p / (p - 1) := by positivity
  have hc : a ^ (p / (p - 1)) ≤ (2 : ℝ) ^ (14 / (p - 1)) := by
    calc
      _ ≤ (128 : ℝ) ^ (p / (p - 1)) := Real.rpow_le_rpow ha ha128 hq
      _ = (2 : ℝ) ^ (7 * (p / (p - 1))) := by
        rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith : 7 * p ≤ 14) hd.le
  rw [Real.mul_rpow ha hr]
  exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr _)

lemma six_estimates_cost (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) (hp : 1 < q.p) (hp2 : q.p ≤ 2)
    (a : ℝ) (ha : 0 < a) (ha128 : a ≤ 128) :
    (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / a) 6 : ℝ) ≤
      (2 : ℝ) ^ (48 / (q.p - 1)) * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) := by
  have hd : 0 < q.p - 1 := by linarith
  have hu : 0 < q.ε / a := div_pos hε ha
  have h := ScalarHeavyTailEstimator.calls_bound hσ hu hp hp2 6
  have he : q.σ / (q.ε / a) = a * (q.σ / q.ε) := by field_simp
  have hn := scaled_noise_power (div_nonneg hσ hε.le) hp hp2 ha.le ha128
  have hC : 1 ≤ (2 : ℝ) ^ (14 / (q.p - 1)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnoise : 1 + (q.σ / (q.ε / a)) ^ (q.p / (q.p - 1)) ≤
      (2 : ℝ) ^ (14 / (q.p - 1)) * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) := by
    rw [he]
    nlinarith
  have hc : 6 * (2 : ℝ) ^ (28 / (q.p - 1)) * 2 ^ (14 / (q.p - 1)) ≤ 2 ^ (48 / (q.p - 1)) := by
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℝ) * 2 ^ (28 / (q.p - 1)) * 2 ^ (14 / (q.p - 1)) := by
        gcongr
        norm_num
      _ = (2 : ℝ) ^ (3 + 28 / (q.p - 1) + 14 / (q.p - 1)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply (le_div_iff₀ hd).mpr
        have he' : (3 + 28 / (q.p - 1) + 14 / (q.p - 1)) * (q.p - 1) = 3 * (q.p - 1) + 42 := by
          field_simp
          ring
        rw [he']
        linarith
  calc
    _ ≤ 6 * (2 : ℝ) ^ (28 / (q.p - 1)) *
        (1 + (q.σ / (q.ε / a)) ^ (q.p / (q.p - 1))) := by simpa using h
    _ ≤ 6 * (2 : ℝ) ^ (28 / (q.p - 1)) *
        (2 ^ (14 / (q.p - 1)) * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1)))) :=
      mul_le_mul_of_nonneg_left hnoise (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hc (by positivity)

lemma noise_square_bound {r p : ℝ} (hr : 0 ≤ r) (hp : 1 < p) (hp2 : p ≤ 2) :
    r ^ 2 ≤ 1 + r ^ (p / (p - 1)) := by
  have hq := noise_exponent_ge_two hp hp2
  have hn := Real.rpow_nonneg hr (p / (p - 1))
  by_cases hr1 : r ≤ 1
  · have h : r ^ 2 ≤ (1 : ℝ) := by simpa only [one_pow] using pow_le_pow_left₀ hr hr1 2
    linarith
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hq
    rw [Real.rpow_two] at h
    linarith

lemma noise_level_power_bound (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) (hp : 1 < q.p) (hp2 : q.p ≤ 2) :
    (4 : ℝ) ^ ScalarHeavyTailEstimator.noiseLevel q.σ (q.ε / 48) ≤
      (2 : ℝ) ^ (30 : ℕ) * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) := by
  let r := q.σ / q.ε
  let N := ScalarHeavyTailEstimator.noiseLevel q.σ (q.ε / 48)
  have hr : 0 ≤ r := div_nonneg hσ hε.le
  have hs := noise_square_bound hr hp hp2
  have hd := ScalarHeavyTailEstimator.dyadic_ceil_upper (128 * q.σ / (q.ε / 48))
  change (2 : ℝ) ^ N ≤ 2 * max 1 (128 * q.σ / (q.ε / 48)) at hd
  have he : 128 * q.σ / (q.ε / 48) = 6144 * r := by dsimp [r]; ring
  rw [he] at hd
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ N) hd 2
  have hmax : (max 1 (6144 * r)) ^ 2 ≤ 1 + (6144 * r) ^ 2 := by
    rcases le_total 1 (6144 * r) with h | h
    · rw [max_eq_right h]
      nlinarith
    · rw [max_eq_left h]
      nlinarith [sq_nonneg (6144 * r)]
  have hpw : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 N, pow_mul]
  change (4 : ℝ) ^ N ≤ (2 : ℝ) ^ (30 : ℕ) * (1 + r ^ (q.p / (q.p - 1)))
  rw [hpw]
  norm_num at hsq ⊢
  nlinarith [Real.rpow_nonneg hr (q.p / (q.p - 1))]

lemma levels_power_bound (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    (2 : ℝ) ^ levels q ≤ 8 * (1 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε) := by
  let A := q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h := ScalarHeavyTailEstimator.dyadic_ceil_upper
    (4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε)
  have he : 4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε = 4 * A := by dsimp [A]; ring
  change (2 : ℝ) ^ levels q ≤ 2 * max 1 (4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε) at h
  rw [he] at h
  have hm : max 1 (4 * A) ≤ 4 * (1 + A) := by apply max_le <;> linarith
  exact h.trans (by change 2 * max 1 (4 * A) ≤ 8 * (1 + A); linarith)

lemma depth_log_bound (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    (depth q : ℝ) ≤ 32 * (1 + 1 / q.ν) *
      Real.log (2 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε) := by
  let A := q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε
  let L := Real.log (2 + A)
  let T := distance q * (8 * q.H / q.ε) ^ (1 / q.ν)
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by dsimp [T, distance]; positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hL : 1 / 2 ≤ L := hlog2.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + A))
  have hAL : Real.log A ≤ L := Real.log_le_log hA (by linarith : A ≤ 2 + A)
  have hLA : Real.log A = 1 / (1 + q.ν) * Real.log q.H +
      q.ν / (1 + q.ν) * Real.log q.Δ - Real.log q.ε := by
    dsimp only [A]
    rw [Real.log_div (by positivity) hε.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hH, Real.log_rpow hΔ]
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hLT : Real.log T = (5 + 3 / q.ν) * Real.log 2 + (1 + 1 / q.ν) * Real.log A := by
    dsimp only [T, distance]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) hε.ne',
      Real.log_mul (by norm_num) hΔ.ne', Real.log_rpow (by positivity),
      Real.log_div (by positivity) hε.ne', Real.log_mul (by norm_num) hH.ne', h32, h8, hLA]
    field_simp; ring
  have hv : 0 ≤ 1 / q.ν := by positivity
  have hB : 0 ≤ (1 + 1 / q.ν) * L := mul_nonneg (by positivity) (by linarith)
  have hlog : Real.logb 2 (max 1 T) ≤ 5 + 3 / q.ν + 2 * (1 + 1 / q.ν) * L := by
    by_cases hlarge : 1 ≤ T
    · rw [max_eq_right hlarge, Real.logb]
      apply (div_le_iff₀ hlog2pos).mpr
      have h := mul_le_mul_of_nonneg_left hAL (by positivity : 0 ≤ 1 + 1 / q.ν)
      have hprod := mul_nonneg (by linarith : 0 ≤ 2 * Real.log 2 - 1) hB
      rw [hLT]
      nlinarith
    · rw [max_eq_left (le_of_not_ge hlarge)]
      simp only [Real.logb_one]
      positivity
  have hn : 0 ≤ Real.logb 2 (max 1 T) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  have hc := Nat.ceil_lt_add_one hn
  have hdepth : (depth q : ℝ) ≤ 2 + Real.logb 2 (max 1 T) := by
    change ((max 1 ⌈Real.logb 2 (max 1 T)⌉₊ : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le <;> linarith
  have hprod := mul_le_mul_of_nonneg_left hL (show 0 ≤ 1 + 1 / q.ν by positivity)
  change (depth q : ℝ) ≤ 32 * (1 + 1 / q.ν) * L
  rw [show 3 / q.ν = 3 * (1 / q.ν) by ring] at hlog
  nlinarith

lemma discovery_cost_simplified (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2) :
    (discoveryCalls q : ℝ) ≤ (2 : ℝ) ^ (80 / (q.p - 1)) *
      (1 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε +
        (q.σ / q.ε) ^ (q.p / (q.p - 1))) := by
  let A := q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε
  let V := (q.σ / q.ε) ^ (q.p / (q.p - 1))
  let B := 1 + A + V
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hd : 0 < q.p - 1 := by linarith
  have hN : (4 : ℝ) ^ ScalarHeavyTailEstimator.noiseLevel q.σ (q.ε / 48) ≤ 2 ^ (30 : ℕ) * B :=
    (noise_level_power_bound q hσ hε hp hp2).trans (mul_le_mul_of_nonneg_left
      (by dsimp [B, V]; linarith) (by positivity))
  have hJ : (2 : ℝ) ^ levels q ≤ 8 * B := (levels_power_bound q hH hΔ hε).trans
    (by dsimp [B, A]; linarith)
  have hnoise : (q.σ / (q.ε / 48)) ^ (q.p / (q.p - 1)) ≤ (2 : ℝ) ^ (14 / (q.p - 1)) * B := by
    have he : q.σ / (q.ε / 48) = 48 * (q.σ / q.ε) := by field_simp
    rw [he]
    exact (scaled_noise_power (div_nonneg hσ hε.le) hp hp2 (by norm_num : (0 : ℝ) ≤ 48)
      (by norm_num : (48 : ℝ) ≤ 128)).trans
      (mul_le_mul_of_nonneg_left (by dsimp [B, V]; linarith) (by positivity))
  have hfixed : (132 : ℝ) * 2 ^ (30 : ℕ) + 194 * 8 + 33 ≤ 2 ^ (40 / (q.p - 1)) := by
    have hc : (2 : ℝ) ^ (40 : ℝ) ≤ 2 ^ (40 / (q.p - 1)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      apply (le_div_iff₀ hd).mpr
      linarith
    exact (by norm_num : (132 : ℝ) * 2 ^ (30 : ℕ) + 194 * 8 + 33 ≤ 2 ^ (40 : ℝ)).trans hc
  have hvar : (165 : ℝ) * 2 ^ (14 / (q.p - 1)) ≤ 2 ^ (40 / (q.p - 1)) := by
    calc
      _ ≤ (2 : ℝ) ^ (8 : ℝ) * 2 ^ (14 / (q.p - 1)) := by gcongr; norm_num
      _ = (2 : ℝ) ^ (8 + 14 / (q.p - 1)) := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply (le_div_iff₀ hd).mpr
        have he : (8 + 14 / (q.p - 1)) * (q.p - 1) = 8 * (q.p - 1) + 14 := by field_simp
        rw [he]
        linarith
  have hdouble : 2 * (2 : ℝ) ^ (40 / (q.p - 1)) ≤ 2 ^ (42 / (q.p - 1)) := by
    have hepow : 2 * (2 : ℝ) ^ (40 / (q.p - 1)) = 2 ^ (1 + 40 / (q.p - 1)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hepow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (le_div_iff₀ hd).mpr
    have he : (1 + 40 / (q.p - 1)) * (q.p - 1) = q.p - 1 + 40 := by field_simp
    rw [he]
    linarith
  have hcoeff : (132 : ℝ) * 2 ^ (30 : ℕ) + 194 * 8 +
      165 * 2 ^ (14 / (q.p - 1)) + 33 ≤ 2 ^ (42 / (q.p - 1)) := by linarith
  have hinside : 132 * (4 : ℝ) ^ ScalarHeavyTailEstimator.noiseLevel q.σ (q.ε / 48) +
      194 * (2 : ℝ) ^ levels q + 165 * (q.σ / (q.ε / 48)) ^ (q.p / (q.p - 1)) + 33 ≤
      2 ^ (42 / (q.p - 1)) * B := by
    have hc := mul_le_mul_of_nonneg_right hcoeff (by linarith : 0 ≤ B)
    nlinarith
  have houter : 1024 * (2 : ℝ) ^ (28 / (q.p - 1)) * 2 ^ (42 / (q.p - 1)) ≤
      2 ^ (80 / (q.p - 1)) := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (le_div_iff₀ hd).mpr
    have he : (10 + 28 / (q.p - 1) + 42 / (q.p - 1)) * (q.p - 1) = 10 * (q.p - 1) + 70 := by
      field_simp; ring
    rw [he]
    linarith
  have hraw := discovery_cost_bound q hσ hε hp hp2
  change (discoveryCalls q : ℝ) ≤ (2 : ℝ) ^ (80 / (q.p - 1)) * B
  calc
    _ ≤ 1024 * (2 : ℝ) ^ (28 / (q.p - 1)) *
        (2 ^ (42 / (q.p - 1)) * B) :=
      hraw.trans (mul_le_mul_of_nonneg_left hinside (by positivity))
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right houter (by linarith)

lemma execution_cost_raw (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) (hp : 1 < q.p) (hp2 : q.p ≤ 2) :
    (executionCalls q : ℝ) ≤ (discoveryCalls q : ℝ) + 2048 * (2 : ℝ) ^ (48 / (q.p - 1)) *
      (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) * (depth q : ℝ) := by
  have h48 := six_estimates_cost q hσ hε hp hp2 48 (by norm_num) (by norm_num)
  have h96 := six_estimates_cost q hσ hε hp hp2 96 (by norm_num) (by norm_num)
  have hD : (1 : ℝ) ≤ (depth q : ℝ) := by exact_mod_cast depth_pos q
  have h48D : (ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6 : ℝ) ≤
      (2 : ℝ) ^ (48 / (q.p - 1)) * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) * (depth q : ℝ) := by
    apply h48.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hD
      (show 0 ≤ (2 : ℝ) ^ (48 / (q.p - 1)) * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) by positivity)
  have h96D := mul_le_mul_of_nonneg_left h96 (Nat.cast_nonneg (depth q) : (0 : ℝ) ≤ depth q)
  have hnonneg : 0 ≤ (2 : ℝ) ^ (48 / (q.p - 1)) *
      (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) * (depth q : ℝ) := by positivity
  unfold executionCalls attemptCalls
  push_cast
  nlinarith

lemma signal_log_bounds {A : ℝ} (hA : 0 ≤ A) :
    1 / 2 ≤ Real.log (2 + A) ∧ Real.log (2 + A) ≤ 1 + A := by
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + A)
    linarith [Real.log_two_gt_d9]
  · have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + A)
    linarith

lemma execution_cost_simplified (q : LongTails.Setups.ScalarHolderStochastic.Params)
    (hH : 0 < q.H) (hν : 0 < q.ν) (hΔ : 0 < q.Δ) (hε : 0 < q.ε)
    (hσ : 0 ≤ q.σ) (hp : 1 < q.p) (hp2 : q.p ≤ 2) :
    (executionCalls q : ℝ) ≤ (2 : ℝ) ^ (200 / (q.p - 1)) * (1 + 1 / q.ν) *
      (1 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε +
        (q.σ / q.ε) ^ (q.p / (q.p - 1)) *
          Real.log (2 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε)) := by
  let A := q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε
  let V := (q.σ / q.ε) ^ (q.p / (q.p - 1))
  let L := Real.log (2 + A)
  let B := 1 + A + V * L
  let F := (1 + 1 / q.ν) * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨hL, hLA⟩ := signal_log_bounds hA
  have hLp : 0 ≤ L := by dsimp [L]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hd : 0 < q.p - 1 := by linarith
  have hBF : B ≤ F := by dsimp [F]; nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / q.ν) hB]
  have hsum : 1 + A + V ≤ 2 * F := by
    have h := mul_le_mul_of_nonneg_right hL hV
    dsimp only [B, L] at hBF
    nlinarith
  have hdepth := depth_log_bound q hH hν hΔ hε
  have hD : (1 + V) * (depth q : ℝ) ≤ 32 * F := by
    calc
      _ ≤ (1 + V) * (32 * (1 + 1 / q.ν) * L) :=
        mul_le_mul_of_nonneg_left hdepth (by positivity)
      _ = 32 * (1 + 1 / q.ν) * (L + V * L) := by ring
      _ ≤ 32 * F := by
        dsimp only [F, B]
        have h := mul_le_mul_of_nonneg_left hLA (show 0 ≤ 32 * (1 + 1 / q.ν) by positivity)
        nlinarith
  have hsmall : 65536 * (2 : ℝ) ^ (48 / (q.p - 1)) ≤ 2 ^ (80 / (q.p - 1)) := by
    rw [show (65536 : ℝ) = 2 ^ (16 : ℝ) by norm_num, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (le_div_iff₀ hd).mpr
    have he : (16 + 48 / (q.p - 1)) * (q.p - 1) = 16 * (q.p - 1) + 48 := by field_simp
    rw [he]
    linarith
  have hroot : 2048 * (2 : ℝ) ^ (48 / (q.p - 1)) * (1 + V) * (depth q : ℝ) ≤
      2 ^ (80 / (q.p - 1)) * F := by
    calc
      _ = (2048 * (2 : ℝ) ^ (48 / (q.p - 1))) * ((1 + V) * (depth q : ℝ)) := by ring
      _ ≤ (2048 * (2 : ℝ) ^ (48 / (q.p - 1))) * (32 * F) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = (65536 * (2 : ℝ) ^ (48 / (q.p - 1))) * F := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF
  have hdisc : (discoveryCalls q : ℝ) ≤ 2 * (2 : ℝ) ^ (80 / (q.p - 1)) * F := by
    have h := discovery_cost_simplified q hH hΔ hε hσ hp hp2
    have h' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (2 : ℝ) ^ (80 / (q.p - 1)) by positivity)
    dsimp only [A, V] at h'
    nlinarith
  have hlarge : 3 * (2 : ℝ) ^ (80 / (q.p - 1)) ≤ 2 ^ (200 / (q.p - 1)) := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) * 2 ^ (80 / (q.p - 1)) := by gcongr; norm_num
      _ = (2 : ℝ) ^ (2 + 80 / (q.p - 1)) := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply (le_div_iff₀ hd).mpr
        have he : (2 + 80 / (q.p - 1)) * (q.p - 1) = 2 * (q.p - 1) + 80 := by field_simp
        rw [he]
        linarith
  have hraw := execution_cost_raw q hσ hε hp hp2
  have hfinal := mul_le_mul_of_nonneg_right hlarge hF
  change (executionCalls q : ℝ) ≤ (2 : ℝ) ^ (200 / (q.p - 1)) * (1 + 1 / q.ν) * B
  change (executionCalls q : ℝ) ≤ (discoveryCalls q : ℝ) +
    2048 * (2 : ℝ) ^ (48 / (q.p - 1)) * (1 + V) * (depth q : ℝ) at hraw
  dsimp only [F] at hfinal hdisc hroot
  nlinarith

lemma executionCalls_le_publicBudget (q : LongTails.Setups.ScalarHolderStochastic.Params) (hq : LongTails.Setups.ScalarHolderStochastic.spec.valid q) :
    executionCalls q ≤ ⌈(2 : ℝ) ^ (200 / (q.p - 1)) * (1 + 1 / q.ν) *
      (1 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε +
        (q.σ / q.ε) ^ (q.p / (q.p - 1)) *
          Real.log (2 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε))⌉₊ := by
  rcases hq with ⟨hH, hν, hν1, hΔ, hσ, hp, hp2, hε⟩
  have h := execution_cost_simplified q hH hν hΔ hε hσ hp hp2
  exact_mod_cast h.trans (Nat.le_ceil _)

end OracleTemplate.ScalarHolderSearch
