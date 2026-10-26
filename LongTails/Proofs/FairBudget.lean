import LongTails.Proofs.FairTuning
import LongTails.Proofs.MixedNoiseBudget

namespace OracleTemplate.FairVarianceReduction

lemma calls_refresh_only (cfg : Config) (hq : cfg.q = 1) :
    cfg.calls = 2 * cfg.m * cfg.T * cfg.b0 := by
  simp only [Config.calls, Config.batch, Config.isRefresh, hq, Nat.mod_one, beq_self_eq_true,
    ite_true, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

lemma calls_one (cfg : Config) (hT : cfg.T = 1) : cfg.calls = 2 * cfg.m * cfg.b0 := by
  simp [Config.calls, hT, Config.batch, Config.isRefresh]

lemma periodic_refresh_sum_bound (T q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B) :
    (∑ t ∈ Finset.range T, if t % q = 0 then B else 0) ≤ ((T : ℝ) / q + 1) * B := by
  let n := ⌈(T : ℝ) / q⌉₊
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo := Nat.le_ceil ((T : ℝ) / q)
  have hn : T ≤ n * q := by
    have he := (div_le_iff₀ hqr).mp hlo
    exact_mod_cast he
  have hh : (∑ t ∈ Finset.range T, if t % q = 0 then B else 0) ≤
      ∑ t ∈ Finset.range (n * q), if t % q = 0 then B else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    intro t _ _
    split_ifs <;> positivity
  rw [MixedNoise.periodic_values (fun _ => B) n q hq] at hh
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ hB
  exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (T : ℝ) / q)).le

lemma calls_upper (cfg : Config) (hq : 0 < cfg.q) :
    (cfg.calls : ℝ) ≤ 2 * cfg.m * (((cfg.T : ℝ) / cfg.q + 1) * cfg.b0 + cfg.T * cfg.b) := by
  have hsum : (∑ t ∈ Finset.range cfg.T, (cfg.batch t : ℝ)) ≤
      ((cfg.T : ℝ) / cfg.q + 1) * cfg.b0 + cfg.T * cfg.b := by
    calc
      _ ≤ ∑ t ∈ Finset.range cfg.T,
          ((if t % cfg.q = 0 then (cfg.b0 : ℝ) else 0) + cfg.b) := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases h : t % cfg.q = 0
        · simp only [Config.batch, Config.isRefresh, h, beq_self_eq_true,
            ite_true]
          have := Nat.cast_nonneg (α := ℝ) cfg.b
          linarith
        · simp only [Config.batch, Config.isRefresh, beq_iff_eq, h, ite_false, zero_add]
          exact le_rfl
      _ = (∑ t ∈ Finset.range cfg.T, if t % cfg.q = 0 then (cfg.b0 : ℝ) else 0) + cfg.T * cfg.b := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ _ := add_le_add (periodic_refresh_sum_bound cfg.T cfg.q hq cfg.b0 (Nat.cast_nonneg _)) le_rfl
  have he : (cfg.calls : ℝ) = 2 * cfg.m * (∑ t ∈ Finset.range cfg.T, (cfg.batch t : ℝ)) := by
    simp only [Config.calls, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, Finset.mul_sum]
  rw [he]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

lemma tuned_calls_large_period {L κ r Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ)
    (hr : 0 ≤ r) (hε : 0 < ε) (hq : 1 < tunePeriod L κ Δ ε) :
    ((tunedConfig L κ r Δ ε).calls : ℝ) ≤
      (2 : ℝ) ^ 46 * (4 * tuneBlockQuarter L r Δ ε : ℕ) *
        ((r + ε) ^ 2 / ε ^ 2 + tuneIterations L Δ ε +
          tuneIterations L Δ ε * (κ * (r + ε) ^ 2 / (L * ε))) := by
  let cfg := tunedConfig L κ r Δ ε
  let a := (r + ε) ^ 2 / ε ^ 2
  let z := κ * (r + ε) ^ 2 / (L * ε)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hqpos := tunePeriod_pos (Δ := Δ) hL hκ hε
  have hlarge := tunePeriod_large (Δ := Δ) hL hκ hε hq
  have hqratio : (tunePeriod L κ Δ ε : ℝ) * κ * ε / L ≤ 2 := by
    apply (div_le_iff₀ hL).mpr
    nlinarith [hlarge.2]
  have hi : (tunePeriod L κ Δ ε : ℝ) * κ ^ 2 * (r + ε) ^ 2 / L ^ 2 ≤ 2 * z := by
    have he : (tunePeriod L κ Δ ε : ℝ) * κ ^ 2 * (r + ε) ^ 2 / L ^ 2 =
        ((tunePeriod L κ Δ ε : ℝ) * κ * ε / L) * z := by
      dsimp [z]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hqratio hz
  have hb : (cfg.b : ℝ) ≤ 2 + (2 : ℝ) ^ 44 * z := by
    have hh := tuneIncrementBatch_upper L κ r Δ ε
    change (cfg.b : ℝ) ≤ _ at hh
    have he : (2 : ℝ) ^ 43 * (tunePeriod L κ Δ ε : ℝ) * κ ^ 2 * (r + ε) ^ 2 / L ^ 2 =
        (2 : ℝ) ^ 43 * ((tunePeriod L κ Δ ε : ℝ) * κ ^ 2 * (r + ε) ^ 2 / L ^ 2) := by ring
    rw [he] at hh
    nlinarith
  have hb0 : (cfg.b0 : ℝ) ≤ (2 : ℝ) ^ 21 * a := by
    simpa only [cfg, tunedConfig, a, mul_div_assoc] using tuneRefreshBatch_upper hr hε
  have hf : (cfg.T : ℝ) / cfg.q + 1 ≤ (cfg.T : ℝ) * κ * ε / L + 2 :=
    tune_refresh_frequency hL hκ hε
  have hrefresh : ((cfg.T : ℝ) / cfg.q + 1) * cfg.b0 ≤
      (2 : ℝ) ^ 21 * cfg.T * z + (2 : ℝ) ^ 22 * a := by
    have hh := mul_le_mul hf hb0 (Nat.cast_nonneg cfg.b0)
      (show 0 ≤ (cfg.T : ℝ) * κ * ε / L + 2 by positivity)
    have he : ((cfg.T : ℝ) * κ * ε / L + 2) * ((2 : ℝ) ^ 21 * a) =
        (2 : ℝ) ^ 21 * cfg.T * z + (2 : ℝ) ^ 22 * a := by
      dsimp [a, z]
      field_simp
    exact hh.trans_eq he
  have hinner := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg cfg.T)
  have hc := calls_upper cfg hqpos
  have hs : ((cfg.T : ℝ) / cfg.q + 1) * cfg.b0 + cfg.T * cfg.b ≤
      (2 : ℝ) ^ 45 * (a + cfg.T + cfg.T * z) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg cfg.T) hz]
  have hh := hc.trans (mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * (cfg.m : ℝ) by positivity))
  change (cfg.calls : ℝ) ≤ (2 : ℝ) ^ 46 * cfg.m * (a + cfg.T + cfg.T * z)
  nlinarith

lemma tuned_calls_factor {L κ r Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ)
    (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    ((tunedConfig L κ r Δ ε).calls : ℝ) ≤
      (2 : ℝ) ^ 57 * (4 * tuneBlockQuarter L r Δ ε : ℕ) *
        (tuneScale L r Δ ε + min (κ * ε) L * (r + ε) ^ 2 * Δ / ε ^ 4) := by
  let cfg := tunedConfig L κ r Δ ε
  let a := (r + ε) ^ 2 / ε ^ 2
  let x := L * Δ / ε ^ 2
  let w := min (κ * ε) L * (r + ε) ^ 2 * Δ / ε ^ 4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hm : 0 ≤ (cfg.m : ℝ) := Nat.cast_nonneg _
  have hA : tuneScale L r Δ ε = a + x := by dsimp [tuneScale, a, x]; ring
  have hb0 : (cfg.b0 : ℝ) ≤ (2 : ℝ) ^ 21 * a := by
    simpa only [cfg, tunedConfig, a, mul_div_assoc] using tuneRefreshBatch_upper hr hε
  change (cfg.calls : ℝ) ≤ (2 : ℝ) ^ 57 * cfg.m * (tuneScale L r Δ ε + w)
  rw [hA]
  by_cases hT1 : cfg.T = 1
  · have hc := calls_one cfg hT1
    have hcall : (cfg.calls : ℝ) = 2 * cfg.m * cfg.b0 := by exact_mod_cast hc
    rw [hcall]
    have hh := mul_le_mul_of_nonneg_left hb0 (show 0 ≤ 2 * (cfg.m : ℝ) by positivity)
    have hh' : 2 * (cfg.m : ℝ) * ((2 : ℝ) ^ 21 * a) ≤ (2 : ℝ) ^ 57 * cfg.m * (a + x + w) := by
      have := mul_nonneg hm ha
      have := mul_nonneg hm hx
      have := mul_nonneg hm hw
      nlinarith
    exact hh.trans hh'
  · have hT : 2 ≤ cfg.T := by have := tuneIterations_pos L Δ ε; change 0 < cfg.T at this; omega
    have hTupper : (cfg.T : ℝ) ≤ 1024 * x := by
      have hh := tuneIterations_large_upper (ε := ε) hL.le hΔ hT
      simpa only [cfg, tunedConfig, x, mul_div_assoc, mul_assoc] using hh
    by_cases hq1 : cfg.q = 1
    · have hc := calls_refresh_only cfg hq1
      have hcall : (cfg.calls : ℝ) = 2 * cfg.m * cfg.T * cfg.b0 := by exact_mod_cast hc
      rw [hcall]
      have hmin := tunePeriod_one_lower hL hκ hε hT hq1
      have hxa : x * a ≤ 2 * w := by
        have hh := mul_le_mul_of_nonneg_right hmin
          (show 0 ≤ (r + ε) ^ 2 * Δ / ε ^ 4 by positivity)
        dsimp [x, a, w]
        have he : L * Δ / ε ^ 2 * ((r + ε) ^ 2 / ε ^ 2) = L * ((r + ε) ^ 2 * Δ / ε ^ 4) := by ring
        rw [he]
        calc
          _ = 2 * (L / 2 * ((r + ε) ^ 2 * Δ / ε ^ 4)) := by ring
          _ ≤ 2 * (min (κ * ε) L * ((r + ε) ^ 2 * Δ / ε ^ 4)) :=
            mul_le_mul_of_nonneg_left hh (by norm_num)
          _ = _ := by ring
      have hTa := mul_le_mul_of_nonneg_right hTupper ha
      have hTb0 := mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg cfg.T)
      have hscalar : (cfg.T : ℝ) * cfg.b0 ≤ (2 : ℝ) ^ 33 * w := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hscalar (show 0 ≤ 2 * (cfg.m : ℝ) by positivity)
      have hbound : 2 * (cfg.m : ℝ) * ((2 : ℝ) ^ 33 * w) ≤ (2 : ℝ) ^ 57 * cfg.m * (a + x + w) := by
        have := mul_nonneg hm ha
        have := mul_nonneg hm hx
        have := mul_nonneg hm hw
        nlinarith
      exact (by nlinarith [hh] : 2 * (cfg.m : ℝ) * cfg.T * cfg.b0 ≤ 2 * cfg.m * ((2 : ℝ) ^ 33 * w)).trans hbound
    · have hq : 1 < tunePeriod L κ Δ ε := by
        have := tunePeriod_pos (Δ := Δ) hL hκ hε
        change cfg.q > 0 at this
        change cfg.q > 1
        omega
      have hlarge := tunePeriod_large (Δ := Δ) hL hκ hε hq
      let z := κ * (r + ε) ^ 2 / (L * ε)
      have hz : 0 ≤ z := by dsimp [z]; positivity
      have hxz : x * z = w := by
        dsimp [x, z, w]
        rw [min_eq_left hlarge.1.le]
        field_simp
      have hTz := mul_le_mul_of_nonneg_right hTupper hz
      have hscalar : a + (cfg.T : ℝ) + cfg.T * z ≤ 1024 * (a + x + w) := by
        rw [← hxz]
        nlinarith
      have hc := tuned_calls_large_period hL hκ hr hε hq
      change (cfg.calls : ℝ) ≤ (2 : ℝ) ^ 46 * cfg.m * (a + cfg.T + cfg.T * z) at hc
      have hh := mul_le_mul_of_nonneg_left hscalar (show 0 ≤ (2 : ℝ) ^ 46 * (cfg.m : ℝ) by positivity)
      have hsum : 0 ≤ (cfg.m : ℝ) * (a + x + w) := by positivity
      nlinarith

lemma tuned_calls_simplified {L κ r Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ)
    (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (tunedConfig L κ r Δ ε).calls ≤
      ⌈(2 : ℝ) ^ 66 * (1 + Real.log (((r + ε) ^ 2 + L * Δ) / ε ^ 2)) *
        (((r + ε) ^ 2 + L * Δ) / ε ^ 2 + min (κ * ε) L * (r + ε) ^ 2 * Δ / ε ^ 4)⌉₊ := by
  have hc := tuned_calls_factor hL hκ hr hΔ hε
  have hm := tune_block_size hL.le hr hΔ hε
  have hA := tuneScale_ge_one hL.le hr hΔ hε
  have hfactor : 0 ≤ tuneScale L r Δ ε + min (κ * ε) L * (r + ε) ^ 2 * Δ / ε ^ 4 := by positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (2 : ℝ) ^ 57 by positivity)) hfactor
  have he : (2 : ℝ) ^ 57 * (512 * (1 + Real.log (tuneScale L r Δ ε))) =
      (2 : ℝ) ^ 66 * (1 + Real.log (tuneScale L r Δ ε)) := by ring
  rw [he] at hh
  have hb := hc.trans hh
  have hceil := Nat.le_ceil ((2 : ℝ) ^ 66 * (1 + Real.log (tuneScale L r Δ ε)) *
    (tuneScale L r Δ ε + min (κ * ε) L * (r + ε) ^ 2 * Δ / ε ^ 4))
  exact_mod_cast hb.trans hceil

end OracleTemplate.FairVarianceReduction
