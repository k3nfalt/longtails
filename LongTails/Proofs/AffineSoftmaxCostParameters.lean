import LongTails.Proofs.AffineSoftmaxOuterParameters
import LongTails.Proofs.AffineSoftmaxMultilevelCost

namespace LongTails.Proofs.AffineSoftmaxCostParameters

open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxAcceleration
open AffineSoftmaxOuterParameters

lemma restartRounds_le_of_ratio {d δ : ℝ} {k : ℕ} (h : d / δ ≤ (2 : ℝ) ^ k) :
    restartRounds d δ ≤ k := by
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  exact_mod_cast h

lemma compiler_noise_ratio {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    G / (compilerFloor G D r ε * r) =
      (G * D ^ 2 / (ε * r)) / ((compilerDepth G D r ε : ℝ) ^ 2 * (compilerScale D r) ^ 2) := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  have hs := (compilerScale_bounds hr hrD).2.2
  rw [compilerFloor, ← hs]
  field_simp

lemma compiler_search_depth {G D r ε : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) :
    restartRounds (G * r) (compilerFloor G D r ε * r ^ 2 / 32768) ≤
      6 * compilerDepth G D r ε := by
  let H := compilerDepth G D r ε
  let Q := G * D ^ 2 / (ε * r)
  let t := compilerScale D r
  have hf := compilerFloor_pos hr hrD hε (G := G)
  have hH : 3 ≤ H := compilerDepth_ge_three G D r ε
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have ht : 1 ≤ t := (compilerScale_bounds hr hrD).1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hden : 1 ≤ (H : ℝ) ^ 2 * t ^ 2 := by
    calc
      (1 : ℝ) = 1 ^ 2 * 1 ^ 2 := by norm_num
      _ ≤ (H : ℝ) ^ 2 * t ^ 2 := by gcongr; linarith
  have he : G * r / (compilerFloor G D r ε * r ^ 2 / 32768) =
      32768 * (Q / ((H : ℝ) ^ 2 * t ^ 2)) := by
    rw [← compiler_noise_ratio hr hrD hε]
    field_simp
  apply restartRounds_le_of_ratio
  rw [he]
  calc
    _ ≤ (32768 : ℝ) * Q := by gcongr; exact div_le_self hQ hden
    _ ≤ (2 : ℝ) ^ 15 * (2 : ℝ) ^ (H - 3) := by
      norm_num only [show (2 : ℝ) ^ 15 = 32768 by norm_num]
      gcongr
      exact compilerDepth_power G D r ε
    _ = (2 : ℝ) ^ (15 + (H - 3)) := by rw [pow_add]
    _ ≤ (2 : ℝ) ^ (6 * H) := by apply pow_le_pow_right₀ (by norm_num); omega

lemma compiler_final_tolerance_ratio {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    G * r / (compilerFloor G D r ε * r ^ 2 / (100000 * (compilerDepth G D r ε : ℝ) ^ 3)) =
      100000 * (compilerDepth G D r ε : ℝ) * (G * D ^ 2 / (ε * r)) / (compilerScale D r) ^ 2 := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  have hs := (compilerScale_bounds hr hrD).2.2
  rw [compilerFloor, ← hs]
  field_simp

lemma compiler_final_prox_depth {G D r ε : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) :
    restartRounds (G * r) (compilerFloor G D r ε * r ^ 2 / (100000 * (compilerDepth G D r ε : ℝ) ^ 3)) ≤
      8 * compilerDepth G D r ε := by
  let H := compilerDepth G D r ε
  let Q := G * D ^ 2 / (ε * r)
  let t := compilerScale D r
  have hH : 3 ≤ H := compilerDepth_ge_three G D r ε
  have ht : 1 ≤ t := (compilerScale_bounds hr hrD).1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hHp : (H : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast (Nat.le_of_lt H.lt_two_pow_self)
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  apply restartRounds_le_of_ratio
  rw [compiler_final_tolerance_ratio hr hrD hε]
  change 100000 * (H : ℝ) * Q / t ^ 2 ≤ _
  calc
    _ ≤ 100000 * (H : ℝ) * Q := div_le_self (by positivity) ht2
    _ ≤ (2 : ℝ) ^ 17 * (2 : ℝ) ^ H * (2 : ℝ) ^ (H - 3) := by
      gcongr
      · norm_num
      · exact compilerDepth_power G D r ε
    _ = (2 : ℝ) ^ (17 + H + (H - 3)) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (8 * H) := by apply pow_le_pow_right₀ (by norm_num); omega

lemma compiler_multilevel_base_depth {G D r ε : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) :
    restartRounds (G * r) (compilerFloor G D r ε * r ^ 2 /
      (2 * 100000 * (compilerDepth G D r ε : ℝ) ^ 3 * (2 + 12 * ((5 * compilerDepth G D r ε : ℕ) : ℝ)))) ≤
      10 * compilerDepth G D r ε := by
  let H := compilerDepth G D r ε
  let Q := G * D ^ 2 / (ε * r)
  let t := compilerScale D r
  have hf := compilerFloor_pos hr hrD hε (G := G)
  have hH : 3 ≤ H := compilerDepth_ge_three G D r ε
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have ht : 1 ≤ t := (compilerScale_bounds hr hrD).1
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hHp : (H : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast (Nat.le_of_lt H.lt_two_pow_self)
  have he : G * r / (compilerFloor G D r ε * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * ((5 * H : ℕ) : ℝ)))) =
      2 * (2 + 60 * (H : ℝ)) * (G * r / (compilerFloor G D r ε * r ^ 2 / (100000 * (H : ℝ) ^ 3))) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  apply restartRounds_le_of_ratio
  rw [he, compiler_final_tolerance_ratio hr hrD hε]
  change 2 * (2 + 60 * (H : ℝ)) * (100000 * (H : ℝ) * Q / t ^ 2) ≤ _
  calc
    _ ≤ 2 * (61 * (H : ℝ)) * (100000 * (H : ℝ) * Q) := by
      gcongr
      · linarith
      · exact div_le_self (by positivity) ht2
    _ = 12200000 * (H : ℝ) ^ 2 * Q := by ring
    _ ≤ (2 : ℝ) ^ 24 * ((2 : ℝ) ^ H) ^ 2 * (2 : ℝ) ^ (H - 3) := by
      gcongr
      · norm_num
      · exact compilerDepth_power G D r ε
    _ = (2 : ℝ) ^ (24 + H * 2 + (H - 3)) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (10 * H) := by apply pow_le_pow_right₀ (by norm_num); omega

lemma compilerCap_scaled_bound {G D r ε : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    compilerCap G D r ε * r * D / ε ≤
      4 * (compilerDepth G D r ε : ℝ) ^ 2 * (G * D ^ 2 / (ε * r)) := by
  let H := compilerDepth G D r ε
  let Q := G * D ^ 2 / (ε * r)
  let t := compilerScale D r
  have hD : 0 < D := hr.trans_le hrD
  have ht : 1 ≤ t := (compilerScale_bounds hr hrD).1
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast compilerDepth_ge_three G D r ε
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hz : 1 ≤ D / r := (one_le_div hr).2 hrD
  have heQ : Q = (G * D / ε) * (D / r) := by dsimp [Q]; field_simp
  have hzQ : D / r ≤ Q := by
    rw [heQ]
    have hh := mul_le_mul_of_nonneg_right ((one_le_div hε).2 hsmall.le) (div_pos hD hr).le
    simpa only [one_mul] using hh
  have hgQ : G * D / ε ≤ Q := by
    rw [heQ]
    exact le_mul_of_one_le_right (by positivity) hz
  have hsmallpart : G * D / ε ≤ (H : ℝ) ^ 2 * Q := by
    calc
      _ ≤ Q := hgQ
      _ ≤ (H : ℝ) ^ 2 * Q := le_mul_of_one_le_left hQ (by nlinarith)
  have hlargepart : D / (t * r) ≤ Q := by
    calc
      _ = (D / r) / t := by ring
      _ ≤ D / r := div_le_self (by positivity) ht
      _ ≤ Q := hzQ
  have he : compilerCap G D r ε * r * D / ε =
      2 * (H : ℝ) ^ 2 * (D / (t * r)) + 2 * (G * D / ε) := by
    dsimp only [compilerCap, compilerFloor, H, t]
    field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hlargepart (show 0 ≤ 2 * (H : ℝ) ^ 2 by positivity)
  change _ ≤ 4 * (H : ℝ) ^ 2 * Q
  nlinarith only [hh, hsmallpart]

lemma compiler_multilevel_depth {G D r ε μ : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) (hμ : 0 ≤ μ) (hμcap : μ ≤ compilerCap G D r ε) :
    restartRounds (μ ^ 2 * r ^ 2 / (100000 * (compilerDepth G D r ε : ℝ) ^ 3))
      ((ε / (1000 * D)) ^ 2) ≤ 5 * compilerDepth G D r ε := by
  let H := compilerDepth G D r ε
  let Q := G * D ^ 2 / (ε * r)
  have hD : 0 < D := hr.trans_le hrD
  have hH : 3 ≤ H := compilerDepth_ge_three G D r ε
  have hHp : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hH)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscaled : μ * r * D / ε ≤ 4 * (H : ℝ) ^ 2 * Q := by
    calc
      _ ≤ compilerCap G D r ε * r * D / ε := by gcongr
      _ ≤ _ := compilerCap_scaled_bound hG hr hrD hε hsmall
  have he : (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) / ((ε / (1000 * D)) ^ 2) =
      10 * (μ * r * D / ε) ^ 2 / (H : ℝ) ^ 3 := by field_simp; ring
  have hbound : (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)) / ((ε / (1000 * D)) ^ 2) ≤
      160 * (H : ℝ) * Q ^ 2 := by
    rw [he]
    calc
      _ ≤ 10 * (4 * (H : ℝ) ^ 2 * Q) ^ 2 / (H : ℝ) ^ 3 := by gcongr
      _ = _ := by field_simp; ring
  have hHp2 : (H : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast (Nat.le_of_lt H.lt_two_pow_self)
  apply restartRounds_le_of_ratio
  calc
    _ ≤ 160 * (H : ℝ) * Q ^ 2 := hbound
    _ ≤ (2 : ℝ) ^ 8 * (2 : ℝ) ^ H * ((2 : ℝ) ^ (H - 3)) ^ 2 := by
      gcongr
      · norm_num
      · exact compilerDepth_power G D r ε
    _ = (2 : ℝ) ^ (8 + H + (H - 3) * 2) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (5 * H) := by apply pow_le_pow_right₀ (by norm_num); omega

lemma regularized_coefficient_bound {S floor : ℝ} (hS : 0 ≤ S) (hf : 0 < floor) :
    16 * Real.sqrt ((S + floor) / floor) + 4 ≤ 20 * (1 + Real.sqrt (S / floor)) := by
  have hs := Real.sq_sqrt (div_nonneg hS hf.le)
  have hp := Real.sqrt_nonneg (S / floor)
  have he : (S + floor) / floor = S / floor + 1 := by field_simp
  have hh : Real.sqrt ((S + floor) / floor) ≤ 1 + Real.sqrt (S / floor) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [he]
      nlinarith
  linarith

lemma outer_cost_scalar_bound {m H b J A U T Ms Mp Mm : ℝ}
    (hm : 1 ≤ m) (hH : 3 ≤ H) (hb : 0 ≤ b) (hbH : b ≤ 10 * H)
    (hJ : J = 5 * H) (hA : 0 ≤ A) (hAU : A ≤ 20 * (1 + U))
    (hU : 0 ≤ U) (hT : 0 ≤ T) (hMs : 0 ≤ Ms) (hMsH : Ms ≤ 10 * H)
    (hMp : 0 ≤ Mp) (hMpH : Mp ≤ 8 * H) (hMm : 0 ≤ Mm) (hMmH : Mm ≤ 10 * H) :
    (2 * H + 9) * (m + b * m + b * (A * Ms + 33554432 * T)) +
      (m + (A * Mp + 102400000 * H ^ 3 * T) +
        (A * (3 * Mm + 4) + 204800000 * H ^ 3 * (2 + 12 * J) * (1 + 3 * J / 2) * T)) ≤
      200000000000 * H ^ 5 * (m + U + T) := by
  have hH0 : 0 ≤ H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have h12 : 2 + 12 * J ≤ 61 * H := by rw [hJ]; linarith
  have h3 : 1 + 3 * J / 2 ≤ 8 * H := by rw [hJ]; linarith
  have hdet : 3 * Mm + 4 ≤ 32 * H := by linarith
  have hsearch : (2 * H + 9) * (m + b * m + b * (A * Ms + 33554432 * T)) ≤
      110 * H ^ 2 * m + 20000 * H ^ 3 * (1 + U) + 3355443200 * H ^ 2 * T := by
    calc
      _ ≤ (10 * H) * (m + (10 * H) * m + (10 * H) * ((20 * (1 + U)) * (10 * H) + 33554432 * T)) := by
        gcongr
        linarith
      _ ≤ (10 * H) * ((11 * H) * m + (10 * H) * ((20 * (1 + U)) * (10 * H) + 33554432 * T)) := by
        gcongr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hH1) hm0]
      _ = _ := by ring
  have hprox : A * Mp + 102400000 * H ^ 3 * T ≤
      160 * H * (1 + U) + 102400000 * H ^ 3 * T := by
    apply add_le_add_left
    calc
      A * Mp ≤ (20 * (1 + U)) * (8 * H) := by gcongr
      _ = _ := by ring
  have hml : A * (3 * Mm + 4) + 204800000 * H ^ 3 * (2 + 12 * J) * (1 + 3 * J / 2) * T ≤
      640 * H * (1 + U) + 99942400000 * H ^ 5 * T := by
    calc
      _ ≤ (20 * (1 + U)) * (32 * H) + 204800000 * H ^ 3 * (61 * H) * (8 * H) * T := by
        gcongr
      _ = _ := by ring
  have h25 : H ^ 2 ≤ H ^ 5 := pow_le_pow_right₀ hH1 (by omega)
  have h35 : H ^ 3 ≤ H ^ 5 := pow_le_pow_right₀ hH1 (by omega)
  have h15 : H ≤ H ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hH1 (show 1 ≤ 5 by omega)
  have h05 : 1 ≤ H ^ 5 := one_le_pow₀ hH1
  have hsum : 0 ≤ m + U + T := by positivity
  have hmS : m ≤ m + U + T := by linarith
  have huS : 1 + U ≤ m + U + T := by linarith
  have htS : T ≤ m + U + T := by linarith
  calc
    _ ≤ (110 * H ^ 2 * m + 20000 * H ^ 3 * (1 + U) + 3355443200 * H ^ 2 * T) +
        (m + (160 * H * (1 + U) + 102400000 * H ^ 3 * T) +
          (640 * H * (1 + U) + 99942400000 * H ^ 5 * T)) := by linarith only [hsearch, hprox, hml]
    _ ≤ (110 * H ^ 5 * (m + U + T) + 20000 * H ^ 5 * (m + U + T) + 3355443200 * H ^ 5 * (m + U + T)) +
        (H ^ 5 * (m + U + T) + (160 * H ^ 5 * (m + U + T) + 102400000 * H ^ 5 * (m + U + T)) +
          (640 * H ^ 5 * (m + U + T) + 99942400000 * H ^ 5 * (m + U + T))) := by
      gcongr
      exact hmS.trans (le_mul_of_one_le_left hsum h05)
    _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ H ^ 5 by positivity) hsum]

lemma compiler_cost_cancellations {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    (compilerScale D r) ^ 2 / compilerFloor G D r ε = D ^ 2 / (ε * (compilerDepth G D r ε : ℝ) ^ 2) ∧
    compilerScale D r / ((compilerFloor G D r ε) ^ 2 * r ^ 2) = D ^ 2 / (ε ^ 2 * (compilerDepth G D r ε : ℝ) ^ 4) := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  have hs := (compilerScale_bounds hr hrD).2.2
  rw [compilerFloor, ← hs]
  constructor <;> field_simp

lemma compiler_cost_cancellation_bounds {G D r ε S V : ℝ} (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hS : 0 ≤ S) (hV : 0 ≤ V) :
    compilerScale D r * Real.sqrt (S / compilerFloor G D r ε) ≤ D * Real.sqrt (S / ε) ∧
    compilerScale D r * (V / ((compilerFloor G D r ε) ^ 2 * r ^ 2)) ≤ V * D ^ 2 / ε ^ 2 := by
  let t := compilerScale D r
  let floor := compilerFloor G D r ε
  let H := compilerDepth G D r ε
  have hD : 0 < D := hr.trans_le hrD
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hf : 0 < floor := compilerFloor_pos hr hrD hε
  have hH : (3 : ℝ) ≤ H := by exact_mod_cast compilerDepth_ge_three G D r ε
  have hH2 : 1 ≤ (H : ℝ) ^ 2 := by nlinarith
  have hH4 : 1 ≤ (H : ℝ) ^ 4 := by nlinarith [sq_nonneg ((H : ℝ) ^ 2 - 1)]
  have hc := compiler_cost_cancellations hr hrD hε (G := G)
  have hsmooth : t ^ 2 * (S / floor) = (D ^ 2 * (S / ε)) / (H : ℝ) ^ 2 := by
    calc
      _ = (t ^ 2 / floor) * S := by ring
      _ = (D ^ 2 / (ε * (H : ℝ) ^ 2)) * S := by rw [hc.1]
      _ = _ := by ring
  have hsmoothle : t ^ 2 * (S / floor) ≤ D ^ 2 * (S / ε) := by
    rw [hsmooth]
    exact div_le_self (by positivity) hH2
  have hnoise : t * (V / (floor ^ 2 * r ^ 2)) = (V * D ^ 2 / ε ^ 2) / (H : ℝ) ^ 4 := by
    calc
      _ = V * (t / (floor ^ 2 * r ^ 2)) := by ring
      _ = V * (D ^ 2 / (ε ^ 2 * (H : ℝ) ^ 4)) := by rw [hc.2]
      _ = _ := by ring
  constructor
  · have hl := Real.sq_sqrt (div_nonneg hS hf.le)
    have hrhs := Real.sq_sqrt (div_nonneg hS hε.le)
    have hp := Real.sqrt_nonneg (S / floor)
    have hq := Real.sqrt_nonneg (S / ε)
    have heL : (t * Real.sqrt (S / floor)) ^ 2 = t ^ 2 * (S / floor) := by rw [mul_pow, hl]
    have heR : (D * Real.sqrt (S / ε)) ^ 2 = D ^ 2 * (S / ε) := by rw [mul_pow, hrhs]
    change t * Real.sqrt (S / floor) ≤ D * Real.sqrt (S / ε)
    nlinarith [mul_nonneg ht.le hp, mul_nonneg hD.le hq]
  · change t * (V / (floor ^ 2 * r ^ 2)) ≤ _
    rw [hnoise]
    exact div_le_self (by positivity) hH4

end LongTails.Proofs.AffineSoftmaxCostParameters
