import LongTails.Proofs.AffineSoftmaxOuterStopping

namespace LongTails.Proofs.AffineSoftmaxOuterParameters

open LongTails.Algorithms.AffineSoftmaxOuter

lemma compilerScale_bounds {D r : ℝ} (hr : 0 < r) (hrD : r ≤ D) :
    1 ≤ compilerScale D r ∧ compilerScale D r ≤ D / r ∧
      (compilerScale D r) ^ 3 * r ^ 2 = D ^ 2 := by
  have hz : 1 ≤ D / r := (one_le_div hr).2 hrD
  have hzp : 0 < D / r := lt_of_lt_of_le zero_lt_one hz
  have ht : 1 ≤ compilerScale D r := Real.one_le_rpow hz (by norm_num)
  have hu : compilerScale D r ≤ D / r := by
    calc
      _ ≤ (D / r) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
      _ = _ := Real.rpow_one _
  have hc : (compilerScale D r) ^ 3 = (D / r) ^ 2 := by
    change ((D / r) ^ (2 / 3 : ℝ)) ^ 3 = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzp.le]
    norm_num
  refine ⟨ht, hu, ?_⟩
  rw [hc]
  field_simp

lemma compilerDepth_power (G D r ε : ℝ) :
    G * D ^ 2 / (ε * r) ≤ (2 : ℝ) ^ (compilerDepth G D r ε - 3) := by
  have hc := Nat.le_pow_clog (by norm_num : 1 < 2) (Nat.ceil (G * D ^ 2 / (ε * r)))
  have hr : (Nat.ceil (G * D ^ 2 / (ε * r)) : ℝ) ≤
      (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (G * D ^ 2 / (ε * r)))) := by exact_mod_cast hc
  simpa only [compilerDepth, Nat.add_sub_cancel_left] using (Nat.le_ceil _).trans hr

lemma compilerDepth_ge_three (G D r ε : ℝ) : 3 ≤ compilerDepth G D r ε := by
  unfold compilerDepth
  omega

lemma compiler_ratio_bounds {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    1 < G * D ^ 2 / (ε * r) ∧ compilerScale D r ≤ G * D ^ 2 / (ε * r) := by
  have hD : 0 < D := hr.trans_le hrD
  have hg : 1 < G * D / ε := (one_lt_div hε).2 hsmall
  have he : G * D ^ 2 / (ε * r) = (G * D / ε) * (D / r) := by field_simp
  have hz : 1 ≤ D / r := (one_le_div hr).2 hrD
  have hlt : D / r < G * D ^ 2 / (ε * r) := by
    rw [he]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hg (div_pos hD hr)
  exact ⟨hz.trans_lt hlt, (compilerScale_bounds hr hrD).2.1.trans hlt.le⟩

lemma compilerDepth_ge_four {G D r ε : ℝ} (hQ : 1 < G * D ^ 2 / (ε * r)) :
    4 ≤ compilerDepth G D r ε := by
  have hc : (1 : ℝ) < (Nat.ceil (G * D ^ 2 / (ε * r)) : ℝ) := hQ.trans_le (Nat.le_ceil _)
  have hcn : 1 < Nat.ceil (G * D ^ 2 / (ε * r)) := by exact_mod_cast hc
  have hp := Nat.clog_pos (by norm_num : 1 < 2) hcn
  unfold compilerDepth
  omega

lemma compilerDepth_log {G D r ε : ℝ} (hQ : 0 < G * D ^ 2 / (ε * r)) :
    Real.log (G * D ^ 2 / (ε * r)) ≤ (compilerDepth G D r ε : ℝ) - 3 := by
  have hh := Real.log_le_log hQ (compilerDepth_power G D r ε)
  rw [Real.log_pow] at hh
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hb := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (compilerDepth G D r ε - 3))
  have hc : ((compilerDepth G D r ε - 3 : ℕ) : ℝ) = (compilerDepth G D r ε : ℝ) - 3 := by
    rw [Nat.cast_sub (compilerDepth_ge_three G D r ε)]
    norm_num
  rw [hc] at hb hh
  linarith

lemma compilerFloor_pos {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    0 < compilerFloor G D r ε := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  unfold compilerFloor
  positivity

lemma compilerFloor_threshold {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    compilerFloor G D r ε * (100 * D ^ 2 / ε) =
      100 * (compilerDepth G D r ε : ℝ) ^ 2 * (compilerScale D r) ^ 2 := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hscale := (compilerScale_bounds hr hrD).2.2
  rw [compilerFloor, ← hscale]
  field_simp

lemma compilerFloor_threshold_ge_one {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    1 ≤ compilerFloor G D r ε * (100 * D ^ 2 / ε) := by
  rw [compilerFloor_threshold hr hrD hε]
  have hH : (3 : ℝ) ≤ compilerDepth G D r ε := by exact_mod_cast compilerDepth_ge_three G D r ε
  have ht := (compilerScale_bounds hr hrD).1
  calc
    (1 : ℝ) ≤ 100 * (3 : ℝ) ^ 2 * 1 ^ 2 := by norm_num
    _ ≤ 100 * (compilerDepth G D r ε : ℝ) ^ 2 * (compilerScale D r) ^ 2 := by gcongr

lemma compilerHorizon_bounds {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) :
    200 * (compilerDepth G D r ε : ℝ) * compilerScale D r ≤ compilerHorizon G D r ε ∧
      (compilerHorizon G D r ε : ℝ) ≤ 201 * (compilerDepth G D r ε : ℝ) * compilerScale D r := by
  have hH : (3 : ℝ) ≤ compilerDepth G D r ε := by exact_mod_cast compilerDepth_ge_three G D r ε
  have ht := (compilerScale_bounds hr hrD).1
  have hprod : 1 ≤ (compilerDepth G D r ε : ℝ) * compilerScale D r := by
    have hh := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ compilerDepth G D r ε by positivity)
    nlinarith
  refine ⟨Nat.le_ceil _, ?_⟩
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 200 * (compilerDepth G D r ε : ℝ) * compilerScale D r by positivity)
  change (Nat.ceil (200 * (compilerDepth G D r ε : ℝ) * compilerScale D r) : ℝ) ≤ _
  nlinarith

lemma compilerHorizon_pos {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) : 0 < compilerHorizon G D r ε := by
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have h := (show 0 < 200 * (compilerDepth G D r ε : ℝ) * compilerScale D r by positivity).trans_le
    (compilerHorizon_bounds hr hrD).1
  exact_mod_cast h

lemma compiler_total_search_failure {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) :
    (compilerHorizon G D r ε : ℝ) * (((2 * compilerDepth G D r ε + 9 : ℕ) : ℝ) *
      (1 / 4 : ℝ) ^ compilerBoost G D r ε) ≤ 1 / 12 := by
  have hN := compilerHorizon_pos hr hrD (G := G) (ε := ε)
  have hNr : (0 : ℝ) < compilerHorizon G D r ε := by exact_mod_cast hN
  have h := AffineSoftmaxOuterExecution.search_boost_count_failure
    (compilerHorizon G D r ε) (compilerDepth G D r ε) hN (compilerDepth_ge_three G D r ε)
  have hh := mul_le_mul_of_nonneg_left h hNr.le
  have he : (compilerHorizon G D r ε : ℝ) * (1 / (12 * (compilerHorizon G D r ε : ℝ))) = 1 / 12 := by field_simp
  rw [he] at hh
  exact hh

lemma compilerCap_ratio {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    compilerCap G D r ε / compilerFloor G D r ε =
      2 + 2 * (G * D ^ 2 / (ε * r)) / ((compilerDepth G D r ε : ℝ) ^ 2 * (compilerScale D r) ^ 2) := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  have hscale := (compilerScale_bounds hr hrD).2.2
  simp only [compilerCap, compilerFloor]
  rw [← hscale]
  field_simp

lemma compiler_modulus_ratio {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) :
    (2 * D + G / compilerFloor G D r ε) / r =
      2 * (D / r) + (G * D ^ 2 / (ε * r)) / ((compilerDepth G D r ε : ℝ) ^ 2 * (compilerScale D r) ^ 2) := by
  have ht : 0 < compilerScale D r := lt_of_lt_of_le zero_lt_one (compilerScale_bounds hr hrD).1
  have hH : (0 : ℝ) < compilerDepth G D r ε := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (compilerDepth_ge_three G D r ε))
  have hscale := (compilerScale_bounds hr hrD).2.2
  simp only [compilerFloor]
  rw [← hscale]
  field_simp

lemma compiler_search_conditions {G D r ε : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    compilerFloor G D r ε ≤ compilerCap G D r ε ∧
      2 * G / r ≤ compilerCap G D r ε ∧
      compilerCap G D r ε / (2 : ℝ) ^ compilerDepth G D r ε ≤ compilerFloor G D r ε ∧
      (2 * D + G / compilerFloor G D r ε) / (2 : ℝ) ^ (compilerDepth G D r ε + 7) < r / 64 := by
  let Q := G * D ^ 2 / (ε * r)
  let H := compilerDepth G D r ε
  let t := compilerScale D r
  have hf := compilerFloor_pos hr hrD hε (G := G)
  have hH : 3 ≤ H := compilerDepth_ge_three G D r ε
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have ht : 1 ≤ t := (compilerScale_bounds hr hrD).1
  have hQ : 1 < Q := (compiler_ratio_bounds hr hrD hε hsmall).1
  have hQpow : Q ≤ (2 : ℝ) ^ (H - 3) := compilerDepth_power G D r ε
  have hden : 1 ≤ (H : ℝ) ^ 2 * t ^ 2 := by
    calc
      (1 : ℝ) = 1 ^ 2 * 1 ^ 2 := by norm_num
      _ ≤ (H : ℝ) ^ 2 * t ^ 2 := by gcongr; linarith
  have hfrac : Q / ((H : ℝ) ^ 2 * t ^ 2) ≤ Q := div_le_self (by linarith) hden
  have hzlt : D / r < Q := by
    have h := mul_lt_mul_of_pos_right ((one_lt_div hε).2 hsmall) (div_pos (hr.trans_le hrD) hr)
    have he : (G * D / ε) * (D / r) = Q := by dsimp [Q]; field_simp
    simpa only [one_mul, he] using h
  have hcr : compilerCap G D r ε / compilerFloor G D r ε ≤ 4 * Q := by
    have he := compilerCap_ratio hr hrD hε (G := G)
    change _ = 2 + 2 * Q / ((H : ℝ) ^ 2 * t ^ 2) at he
    rw [he, mul_div_assoc]
    linarith only [hfrac, hQ]
  have hkr : (2 * D + G / compilerFloor G D r ε) / r ≤ 3 * Q := by
    have he := compiler_modulus_ratio hr hrD hε (G := G)
    change _ = 2 * (D / r) + Q / ((H : ℝ) ^ 2 * t ^ 2) at he
    rw [he]
    linarith
  have hp : 0 < (2 : ℝ) ^ (H - 3) := by positivity
  have hpH : (2 : ℝ) ^ H = 8 * (2 : ℝ) ^ (H - 3) := by
    calc
      _ = (2 : ℝ) ^ ((H - 3) + 3) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hp7 : (2 : ℝ) ^ (H + 7) = 1024 * (2 : ℝ) ^ (H - 3) := by
    calc
      _ = (2 : ℝ) ^ ((H - 3) + 10) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold compilerCap
    have h : 0 < 2 * G / r := by positivity
    linarith
  · unfold compilerCap
    linarith
  · apply (div_le_iff₀ (by positivity)).2
    change compilerCap G D r ε ≤ compilerFloor G D r ε * (2 : ℝ) ^ H
    rw [hpH]
    have hc := (div_le_iff₀ hf).1 hcr
    have hq := mul_le_mul_of_nonneg_right hQpow hf.le
    nlinarith only [hc, hq, mul_pos hp hf]
  · apply (div_lt_iff₀ (by positivity)).2
    change 2 * D + G / compilerFloor G D r ε < r / 64 * (2 : ℝ) ^ (H + 7)
    rw [hp7]
    have hk := (div_le_iff₀ hr).1 hkr
    have hq := mul_le_mul_of_nonneg_right hQpow hr.le
    nlinarith only [hk, hq, mul_pos hp hr]

lemma compiler_log_weight_bound {G D r ε : ℝ} (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    1 + Real.log (3 * (100 * D ^ 2 / ε) * compilerCap G D r ε) ≤ 6 * compilerDepth G D r ε := by
  let Q := G * D ^ 2 / (ε * r)
  let H := compilerDepth G D r ε
  let t := compilerScale D r
  have hD : 0 < D := hr.trans_le hrD
  have hf := compilerFloor_pos hr hrD hε (G := G)
  have hcap : 0 < compilerCap G D r ε := by unfold compilerCap; positivity
  have hH : (3 : ℝ) ≤ H := by exact_mod_cast compilerDepth_ge_three G D r ε
  have ht : 1 ≤ t := (compilerScale_bounds hr hrD).1
  have hQ : 1 < Q := (compiler_ratio_bounds hr hrD hε hsmall).1
  have htQ : t ≤ Q := (compiler_ratio_bounds hr hrD hε hsmall).2
  have hfm : compilerFloor G D r ε * (100 * D ^ 2 / ε) = 100 * (H : ℝ) ^ 2 * t ^ 2 :=
    compilerFloor_threshold hr hrD hε
  have he : 3 * (100 * D ^ 2 / ε) * compilerCap G D r ε = 600 * (H : ℝ) ^ 2 * t ^ 2 + 600 * Q := by
    have hgpart : 3 * (100 * D ^ 2 / ε) * (2 * G / r) = 600 * Q := by dsimp [Q]; field_simp; norm_num
    unfold compilerCap
    nlinarith only [hfm, hgpart]
  apply AffineSoftmaxOuterBounds.log_weight_envelope (by positivity) hH hQ.le
  · rw [he]
    have hfirst : 600 * (H : ℝ) ^ 2 * t ^ 2 ≤ 600 * (H : ℝ) ^ 2 * Q ^ 2 := by gcongr
    have hsecond : 600 * Q ≤ 600 * (H : ℝ) ^ 2 * Q ^ 2 := by
      have hHsq : 1 ≤ (H : ℝ) ^ 2 := by nlinarith
      have hQsq : Q ≤ Q ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hHsq (show 0 ≤ Q ^ 2 by positivity)
      nlinarith only [hQsq, hh]
    nlinarith only [hfirst, hsecond]
  · exact compilerDepth_log (by dsimp [Q] at hQ; linarith)

lemma compilerBoost_bound {G D r ε : ℝ} (hr : 0 < r) (hrD : r ≤ D) (hε : 0 < ε) (hsmall : ε < G * D) :
    compilerBoost G D r ε ≤ 7 * compilerDepth G D r ε := by
  let H := compilerDepth G D r ε
  let N := compilerHorizon G D r ε
  let t := compilerScale D r
  have hH : 3 ≤ H := compilerDepth_ge_three G D r ε
  have ht0 : 0 ≤ t := zero_le_one.trans (compilerScale_bounds hr hrD).1
  have hN : (N : ℝ) ≤ 201 * (H : ℝ) * t := (compilerHorizon_bounds hr hrD).2
  have ht : t ≤ (2 : ℝ) ^ (H - 3) := (compiler_ratio_bounds hr hrD hε hsmall).2.trans
    (compilerDepth_power G D r ε)
  have hHp : (H : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast (Nat.le_of_lt H.lt_two_pow_self)
  have hbase : (120 * N * H : ℕ) ≤ 2 ^ (7 * H) := by
    have hreal : (120 : ℝ) * N * H ≤ (2 : ℝ) ^ (7 * H) := by
      calc
        _ ≤ (24120 : ℝ) * (H : ℝ) ^ 2 * t := by
          have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ (120 : ℝ) * H by positivity)
          nlinarith only [hh]
        _ ≤ (2 : ℝ) ^ 15 * ((2 : ℝ) ^ H) ^ 2 * (2 : ℝ) ^ (H - 3) := by
          gcongr
          norm_num
        _ = (2 : ℝ) ^ (15 + H * 2 + (H - 3)) := by rw [← pow_mul, ← pow_add, ← pow_add]
        _ ≤ (2 : ℝ) ^ (7 * H) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
    exact_mod_cast hreal
  exact Nat.clog_le_of_le_pow hbase

end LongTails.Proofs.AffineSoftmaxOuterParameters
