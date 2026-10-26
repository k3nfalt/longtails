import LongTails.Algorithms.FairTuning
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.FairVarianceReduction

lemma tuneRadius_pos {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) : 0 < tuneRadius r ε := by
  unfold tuneRadius
  positivity

lemma tuneScale_ge_one {L r Δ ε : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    1 ≤ tuneScale L r Δ ε := by
  rw [tuneScale, le_div_iff₀ (sq_pos_of_pos hε)]
  nlinarith [mul_nonneg hL hΔ]

lemma tuneStep_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) : 0 < tuneStep L ε := by
  unfold tuneStep
  positivity

lemma tuneIterations_pos (L Δ ε : ℝ) : 0 < tuneIterations L Δ ε := by
  unfold tuneIterations
  omega

lemma tuneIterations_lower (L Δ ε : ℝ) :
    512 * L * Δ / ε ^ 2 ≤ (tuneIterations L Δ ε : ℝ) := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast (show ⌈512 * L * Δ / ε ^ 2⌉₊ ≤ tuneIterations L Δ ε from le_max_right _ _)

lemma tunePeriod_pos {L κ Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    0 < tunePeriod L κ Δ ε := by
  have hT : (0 : ℝ) < tuneIterations L Δ ε := by exact_mod_cast tuneIterations_pos L Δ ε
  have hd : 0 < κ * ε + L / tuneIterations L Δ ε := by positivity
  exact Nat.ceil_pos.mpr (div_pos hL hd)

lemma tunePeriod_le_iterations {L κ Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    tunePeriod L κ Δ ε ≤ tuneIterations L Δ ε := by
  have hT : (0 : ℝ) < tuneIterations L Δ ε := by exact_mod_cast tuneIterations_pos L Δ ε
  have hd : 0 < κ * ε + L / tuneIterations L Δ ε := by positivity
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hd).mpr
  have he : (L / (tuneIterations L Δ ε : ℝ)) * tuneIterations L Δ ε = L := div_mul_cancel₀ _ hT.ne'
  nlinarith [mul_nonneg (mul_nonneg hκ hε.le) hT.le]

lemma tuneRefreshBatch_pos {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    0 < tuneRefreshBatch r ε := by
  apply Nat.ceil_pos.mpr
  have hR : 0 < r + ε := by positivity
  positivity

lemma tuneIncrementBatch_pos (L κ r Δ ε : ℝ) : 0 < tuneIncrementBatch L κ r Δ ε := by
  unfold tuneIncrementBatch
  omega

lemma tuneBlockQuarter_pos (L r Δ ε : ℝ) : 0 < tuneBlockQuarter L r Δ ε := by
  unfold tuneBlockQuarter
  omega

lemma tuneGradientBound_nonneg {L Δ ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    0 ≤ tuneGradientBound L Δ ε := by
  unfold tuneGradientBound
  have := (tuneStep_pos hL hε).le
  positivity

lemma tuneClip_pos {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) : 0 < tuneClip r ε := by
  unfold tuneClip
  have hR : 0 < r + ε := by positivity
  positivity

lemma tune_step_clip {L r ε : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hε : 0 < ε) :
    L * tuneStep L ε ≤ tuneClip r ε / 2 := by
  have hR : ε ^ 2 ≤ (r + ε) ^ 2 := by nlinarith
  have he : L * tuneStep L ε = ε / 64 := by unfold tuneStep; field_simp
  rw [he, tuneClip]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply (le_div_iff₀ hε).mpr
  norm_num
  nlinarith [sq_pos_of_pos hε]

lemma tuned_batch_pos {L κ r Δ ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) (t : ℕ) :
    0 < (tunedConfig L κ r Δ ε).batch t := by
  unfold Config.batch
  split_ifs
  · exact tuneRefreshBatch_pos hr hε
  · exact tuneIncrementBatch_pos L κ r Δ ε

lemma tunePeriod_large {L κ Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hq : 1 < tunePeriod L κ Δ ε) :
    κ * ε < L ∧ (tunePeriod L κ Δ ε : ℝ) * (κ * ε) ≤ 2 * L := by
  have hT : (0 : ℝ) < tuneIterations L Δ ε := by exact_mod_cast tuneIterations_pos L Δ ε
  let d := κ * ε + L / tuneIterations L Δ ε
  have hd : 0 < d := by dsimp [d]; positivity
  have hx : 1 < L / d := by
    by_contra h
    have hh : tunePeriod L κ Δ ε ≤ 1 := Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using le_of_not_gt h)
    omega
  have hdL : d < L := by have := (lt_div_iff₀ hd).mp hx; linarith
  have hκd : κ * ε ≤ d := by
    dsimp [d]
    have := (div_pos hL hT).le
    linarith
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ L / d from (div_pos hL hd).le)).le
  change (tunePeriod L κ Δ ε : ℝ) ≤ L / d + 1 at hc
  have hh := mul_le_mul_of_nonneg_right hc hd.le
  have he : (L / d + 1) * d = L + d := by field_simp
  rw [he] at hh
  have hmul := mul_le_mul_of_nonneg_left hκd (Nat.cast_nonneg (tunePeriod L κ Δ ε))
  exact ⟨lt_of_le_of_lt hκd hdL, by linarith⟩

lemma tunePeriod_one_lower {L κ Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hT : 2 ≤ tuneIterations L Δ ε) (hq : tunePeriod L κ Δ ε = 1) :
    L / 2 ≤ min (κ * ε) L := by
  have hTr : (2 : ℝ) ≤ tuneIterations L Δ ε := by exact_mod_cast hT
  have hTp : (0 : ℝ) < tuneIterations L Δ ε := by linarith
  have hd : 0 < κ * ε + L / tuneIterations L Δ ε := by positivity
  have hc := Nat.le_ceil (L / (κ * ε + L / tuneIterations L Δ ε))
  change L / (κ * ε + L / tuneIterations L Δ ε) ≤ (tunePeriod L κ Δ ε : ℝ) at hc
  rw [hq, Nat.cast_one] at hc
  have hh := (div_le_iff₀ hd).mp hc
  have hdiv : L / (tuneIterations L Δ ε : ℝ) ≤ L / 2 := by
    apply div_le_div_of_nonneg_left hL.le (by norm_num) hTr
  apply le_min <;> linarith

lemma tune_block_failure {L r Δ ε : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (1 / 4 : ℝ) ^ tuneBlockQuarter L r Δ ε ≤
      1 / ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) := by
  have hA := tuneScale_ge_one hL hr hΔ hε
  have hX : 0 < (2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3 := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) / Real.log 4)
  have hk : Real.log ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) / Real.log 4 ≤
      (tuneBlockQuarter L r Δ ε : ℝ) := by
    unfold tuneBlockQuarter
    push_cast
    linarith
  have hxpow : (2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3 ≤ 4 ^ tuneBlockQuarter L r Δ ε := by
    apply (Real.log_le_log_iff hX (by positivity)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog4).mp hk
  have he := one_div_le_one_div_of_le hX hxpow
  simpa only [one_div, inv_pow] using he

lemma tune_block_size {L r Δ ε : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    ((4 * tuneBlockQuarter L r Δ ε : ℕ) : ℝ) ≤ 512 * (1 + Real.log (tuneScale L r Δ ε)) := by
  have hA := tuneScale_ge_one hL hr hΔ hε
  have hAp : 0 < tuneScale L r Δ ε := by linarith
  have hlogA : 0 ≤ Real.log (tuneScale L r Δ ε) := Real.log_nonneg hA
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog4 : 1 ≤ Real.log 4 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log 4 = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 2
    rw [he]
    norm_num at hh
    linarith
  have hX : 1 ≤ (2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3 := by
    have hp : 1 ≤ (tuneScale L r Δ ε) ^ 3 := one_le_pow₀ hA
    nlinarith
  have hlogX := Real.log_nonneg hX
  have he : Real.log ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) =
      121 * Real.log 2 + 3 * Real.log (tuneScale L r Δ ε) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  have hd : Real.log ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) / Real.log 4 ≤
      121 + 3 * Real.log (tuneScale L r Δ ε) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 4)).mpr
    rw [he]
    nlinarith
  have hc := (Nat.ceil_lt_add_one (div_nonneg hlogX (by linarith : 0 ≤ Real.log 4))).le
  unfold tuneBlockQuarter
  push_cast
  nlinarith

lemma tuneIterations_upper {L Δ ε : ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) :
    (tuneIterations L Δ ε : ℝ) ≤ 1 + 512 * L * Δ / ε ^ 2 := by
  have hx : 0 ≤ 512 * L * Δ / ε ^ 2 := by positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  rw [tuneIterations, Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

lemma tuneIterations_large_upper {L Δ ε : ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (hT : 2 ≤ tuneIterations L Δ ε) :
    (tuneIterations L Δ ε : ℝ) ≤ 1024 * L * Δ / ε ^ 2 := by
  have hx : 1 < 512 * L * Δ / ε ^ 2 := by
    by_contra h
    have hc : ⌈512 * L * Δ / ε ^ 2⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using le_of_not_gt h)
    unfold tuneIterations at hT
    omega
  have hu := tuneIterations_upper (ε := ε) hL hΔ
  have he : 1024 * L * Δ / ε ^ 2 = 2 * (512 * L * Δ / ε ^ 2) := by ring
  rw [he]
  linarith

lemma tuneIterations_scaled {L Δ ε : ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (tuneIterations L Δ ε : ℝ) * ε ^ 2 ≤ ε ^ 2 + 512 * L * Δ := by
  have hu := mul_le_mul_of_nonneg_right (tuneIterations_upper (ε := ε) hL hΔ) (sq_nonneg ε)
  have he : (512 * L * Δ / ε ^ 2) * ε ^ 2 = 512 * L * Δ :=
    div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hε))
  nlinarith

lemma tuneIterations_scale {L r Δ ε : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (tuneIterations L Δ ε : ℝ) ≤ 512 * tuneScale L r Δ ε := by
  have ht := tuneIterations_scaled hL hΔ hε
  have he : tuneScale L r Δ ε * ε ^ 2 = (r + ε) ^ 2 + L * Δ :=
    div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hε))
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)).mp
  nlinarith

lemma tuneGradientBound_scaled {L r Δ ε : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    tuneGradientBound L Δ ε * ε ≤ 10 * ((r + ε) ^ 2 + L * Δ) := by
  have ht := tuneIterations_scaled hL.le hΔ hε
  have hs := Real.sq_sqrt (show 0 ≤ 2 * L * Δ by positivity)
  have hroot : Real.sqrt (2 * L * Δ) * ε ≤ L * Δ + ε ^ 2 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (2 * L * Δ) - ε)]
  have he : L * (tuneIterations L Δ ε : ℝ) * tuneStep L ε * ε =
      (tuneIterations L Δ ε : ℝ) * ε ^ 2 / 64 := by
    unfold tuneStep
    field_simp
  unfold tuneGradientBound
  rw [add_mul, he]
  nlinarith [mul_nonneg hL.le hΔ]

lemma tune_failure_scale {L κ r Δ ε : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let cfg := tunedConfig L κ r Δ ε
    let M := cfg.G + cfg.B + cfg.R + ε
    (1 / 4 : ℝ) ^ tuneBlockQuarter L r Δ ε ≤ ε ^ 2 / ((2 : ℝ) ^ 53 * cfg.T * M ^ 2) := by
  dsimp only
  let S := (r + ε) ^ 2 + L * Δ
  let M := tuneGradientBound L Δ ε + tuneClip r ε + (r + ε) + ε
  have hSp : 0 < S := by
    have hR : 0 < r + ε := by positivity
    dsimp [S]
    positivity
  have hM : 0 < M := by
    have hG := tuneGradientBound_nonneg (Δ := Δ) hL hε
    have hB := tuneClip_pos hr hε
    dsimp [M]
    positivity
  have hMε : M * ε ≤ 67 * (2 : ℝ) ^ 23 * S := by
    have hG := tuneGradientBound_scaled hL hr hΔ hε
    have hB : tuneClip r ε * ε = 64 * (2 : ℝ) ^ 23 * (r + ε) ^ 2 :=
      div_mul_cancel₀ _ hε.ne'
    dsimp [M, S] at *
    nlinarith [mul_nonneg hL.le hΔ]
  have hM2 : M ^ 2 * ε ^ 2 ≤ (67 * (2 : ℝ) ^ 23) ^ 2 * S ^ 2 := by
    have := pow_le_pow_left₀ (mul_nonneg hM.le hε.le) hMε 2
    nlinarith
  have hT := tuneIterations_scale hL.le hr hΔ hε
  have hA := tuneScale_ge_one hL.le hr hΔ hε
  have hid : tuneScale L r Δ ε * ε ^ 2 = S := div_mul_cancel₀ _ (sq_pos_of_pos hε).ne'
  have hden : (2 : ℝ) ^ 53 * (tuneIterations L Δ ε : ℝ) * M ^ 2 ≤
      ε ^ 2 * ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)).mp
    have h1 := mul_le_mul_of_nonneg_left hM2
      (show 0 ≤ (2 : ℝ) ^ 53 * (tuneIterations L Δ ε : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hT
      (show 0 ≤ (2 : ℝ) ^ 53 * (67 * (2 : ℝ) ^ 23) ^ 2 * S ^ 2 by positivity)
    have hs2 : S ^ 2 = (tuneScale L r Δ ε) ^ 2 * ε ^ 4 := by rw [← hid]; ring
    rw [hs2] at h1 h2
    nlinarith [mul_nonneg (show 0 ≤ (tuneScale L r Δ ε) ^ 3 by positivity) (show 0 ≤ ε ^ 4 by positivity)]
  have hf := tune_block_failure hL.le hr hΔ hε
  apply hf.trans
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3)
    (by have := tuneIterations_pos L Δ ε; positivity : 0 < (2 : ℝ) ^ 53 * (tuneIterations L Δ ε : ℝ) * M ^ 2)).mpr
  simpa only [one_mul] using hden

lemma tuneRefreshBatch_upper {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    (tuneRefreshBatch r ε : ℝ) ≤ (2 : ℝ) ^ 21 * (r + ε) ^ 2 / ε ^ 2 := by
  have ha : 1 ≤ (r + ε) ^ 2 / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ 20 * (r + ε) ^ 2 / ε ^ 2 by positivity)).le
  change (tuneRefreshBatch r ε : ℝ) ≤ _ at hc
  have he : (2 : ℝ) ^ 20 * (r + ε) ^ 2 / ε ^ 2 = 1048576 * ((r + ε) ^ 2 / ε ^ 2) := by ring
  have he' : (2 : ℝ) ^ 21 * (r + ε) ^ 2 / ε ^ 2 = 2097152 * ((r + ε) ^ 2 / ε ^ 2) := by ring
  rw [he] at hc
  rw [he']
  linarith

lemma tuneIncrementBatch_upper (L κ r Δ ε : ℝ) :
    (tuneIncrementBatch L κ r Δ ε : ℝ) ≤
      2 + (2 : ℝ) ^ 43 * (tunePeriod L κ Δ ε : ℝ) * κ ^ 2 * (r + ε) ^ 2 / L ^ 2 := by
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ 43 * (tunePeriod L κ Δ ε : ℝ) * κ ^ 2 *
    (r + ε) ^ 2 / L ^ 2 by positivity)).le
  unfold tuneIncrementBatch
  push_cast
  linarith

lemma tune_refresh_frequency {L κ Δ ε : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    (tuneIterations L Δ ε : ℝ) / tunePeriod L κ Δ ε + 1 ≤
      (tuneIterations L Δ ε : ℝ) * κ * ε / L + 2 := by
  have hT : (0 : ℝ) < tuneIterations L Δ ε := by exact_mod_cast tuneIterations_pos L Δ ε
  have hq : (0 : ℝ) < tunePeriod L κ Δ ε := by exact_mod_cast tunePeriod_pos hL hκ hε
  have hd : 0 < κ * ε + L / tuneIterations L Δ ε := by positivity
  have hc := Nat.le_ceil (L / (κ * ε + L / tuneIterations L Δ ε))
  change L / (κ * ε + L / tuneIterations L Δ ε) ≤ (tunePeriod L κ Δ ε : ℝ) at hc
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mp hc) hT.le
  have he : L / (tuneIterations L Δ ε : ℝ) * tuneIterations L Δ ε = L := div_mul_cancel₀ _ hT.ne'
  have hn : (tuneIterations L Δ ε : ℝ) * L ≤
      (tunePeriod L κ Δ ε : ℝ) * κ * ε * tuneIterations L Δ ε + tunePeriod L κ Δ ε * L := by
    nlinarith
  have hratio : (tuneIterations L Δ ε : ℝ) / tunePeriod L κ Δ ε ≤
      (tuneIterations L Δ ε : ℝ) * κ * ε / L + 1 := by
    apply (div_le_iff₀ hq).mpr
    apply (mul_le_mul_iff_right₀ hL).mp
    have he' : ((tuneIterations L Δ ε : ℝ) * κ * ε / L + 1) * tunePeriod L κ Δ ε * L =
        (tunePeriod L κ Δ ε : ℝ) * κ * ε * tuneIterations L Δ ε + tunePeriod L κ Δ ε * L := by
      field_simp
    nlinarith [he', hn]
  linarith

lemma tuned_descent_accuracy {L Δ ε S : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hS : tuneStep L ε * S ≤ Δ + 2 * tuneStep L ε * tuneIterations L Δ ε * (ε / 16) +
      tuneIterations L Δ ε * L * (tuneStep L ε) ^ 2 / 2) :
    S ≤ (tuneIterations L Δ ε : ℝ) * ε := by
  have hη := tuneStep_pos hL hε
  have hT := tuneIterations_pos L Δ ε
  have hTr : (0 : ℝ) < tuneIterations L Δ ε := by exact_mod_cast hT
  have ht := (div_le_iff₀ (sq_pos_of_pos hε)).mp (tuneIterations_lower L Δ ε)
  have hinit : Δ ≤ tuneStep L ε * tuneIterations L Δ ε * ε / 8 := by
    have he : tuneStep L ε * tuneIterations L Δ ε * ε / 8 =
        (tuneIterations L Δ ε : ℝ) * ε ^ 2 / (512 * L) := by unfold tuneStep; ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 512 * L)).mpr
    nlinarith
  have he : (tuneIterations L Δ ε : ℝ) * L * (tuneStep L ε) ^ 2 / 2 =
      tuneStep L ε * tuneIterations L Δ ε * ε / 128 := by
    unfold tuneStep
    field_simp
    ring
  rw [he] at hS
  have hp : 0 ≤ tuneStep L ε * tuneIterations L Δ ε * ε := by positivity
  nlinarith

end OracleTemplate.FairVarianceReduction
