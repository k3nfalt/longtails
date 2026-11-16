import LongTails.Setups.GapGeneralizedSmoothConvex
import LongTails.Proofs.GapCalibratedParameters
import LongTails.Proofs.AdaptiveTransientParameters

namespace LongTails.Proofs.GapTransientParameters

open LongTails.Setups.GapGeneralizedSmoothConvex

noncomputable def scale (p : Params) : ℝ := p.L1 * p.R
noncomputable def logarithm (p : Params) : ℝ := 1 + Real.log (2 + scale p)
noncomputable def gapLog (p : Params) : ℝ := Real.log (p.Δ / (8 * p.ε))
noncomputable def spacing (p : Params) (m : ℕ) : ℝ := GapCalibratedParameters.spacing m (gapLog p)
noncomputable def slope (p : Params) (m : ℕ) : ℝ := p.ε * (p.L1 / 4) * spacing p m / (25 * logarithm p)
noncomputable def peak (p : Params) (m : ℕ) : ℝ := GapCalibratedWeights.peak m (slope p m) (spacing p m)
noncomputable def degree (p : Params) : ℕ := ⌈16 * Real.sqrt (scale p)⌉₊
noncomputable def width (p : Params) : ℝ := 131072 * p.R
noncomputable def coefficient (p : Params) (m : ℕ) : ℝ := peak p m / width p + p.L0 / 1000
noncomputable def threshold (p : Params) (m : ℕ) : ℝ := spacing p m / (64 * p.L1)

lemma logarithm_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ logarithm p := by
  have hq : 0 ≤ scale p := mul_nonneg hp.2.1 hp.2.2.1.le
  have hl := Real.log_nonneg (show 1 ≤ 2 + scale p by linarith)
  unfold logarithm
  linarith

lemma gapLog_ge_half (p : Params) (hp : spec.valid p) : (1 / 2 : ℝ) ≤ gapLog p := by
  have hε := hp.2.2.2.1
  have hΔ := hp.2.2.2.2.2.1
  have hr : 2 ≤ p.Δ / (8 * p.ε) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num [Real.log_div] at hh
  change (1 / 2 : ℝ) ≤ Real.log (p.Δ / (8 * p.ε))
  linarith

lemma spacing_pos (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) : 0 < spacing p m :=
  GapCalibratedParameters.spacing_pos hm (gapLog p) (by linarith [gapLog_ge_half p hp])

lemma spacing_le_one (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) : spacing p m ≤ 1 :=
  (GapCalibratedParameters.spacing_bounds hm (gapLog p) (by linarith [gapLog_ge_half p hp])).1

lemma spacing_lower (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) :
    1 / (4 * (m : ℝ)) ≤ spacing p m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs0 : 0 < Real.sqrt m := by positivity
  have hs : Real.sqrt m ≤ m := by
    have he := Real.sq_sqrt hm0.le
    nlinarith [Real.sqrt_nonneg (m : ℝ)]
  apply le_min
  · apply one_div_le_one_div_of_le hs0
    linarith
  · apply (div_le_div_iff₀ (by positivity : 0 < 4 * (m : ℝ)) (by positivity : 0 < 2 * (m : ℝ))).mpr
    nlinarith [gapLog_ge_half p hp]

lemma degree_valid (p : Params) (hq : 1 ≤ scale p) : 2 ≤ degree p :=
  AdaptiveTransientParameters.degree_ge_two (scale p) hq

lemma width_valid (p : Params) (hq : 1 ≤ scale p) :
    256 * ((degree p : ℝ) * (degree p + 1 : ℕ)) ≤ p.L1 * width p := by
  have hh := AdaptiveTransientParameters.degree_product (scale p) hq
  change (degree p : ℝ) * (degree p + 1 : ℕ) ≤ 306 * scale p at hh
  unfold width scale at *
  nlinarith only [hh, hq]

lemma L1_pos (p : Params) (hp : spec.valid p) (hq : 1 ≤ scale p) : 0 < p.L1 := by
  by_contra hh
  have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hp.2.2.1.le
  change 1 ≤ p.L1 * p.R at hq
  linarith

lemma peak_suppression (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m)
    (hq : 1 ≤ scale p) (hmq : (m : ℝ) ≤ scale p) :
    peak p m * (1 / 2 : ℝ) ^ degree p * p.L1 ≤ p.L0 := by
  have h1 := L1_pos p hp hq
  have hε := hp.2.2.2.1
  have hw := logarithm_ge_one p hp
  have hw0 : 0 < logarithm p := by linarith
  have ht0 := spacing_pos p hp hm
  have ht1 := spacing_le_one p hp hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht : spacing p m ≤ 1 / Real.sqrt m := min_le_left _ _
  have hexp : ((m : ℝ) - 1) * spacing p m ≤ ((m : ℝ) - 1) / Real.sqrt m := by
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ (m : ℝ) - 1 by linarith)
    simpa only [mul_one_div] using hh
  have hratio : spacing p m / (25 * logarithm p) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hcoef : slope p m ≤ p.ε * p.L1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ p.ε * (p.L1 / 4) by positivity)
    unfold slope
    convert hh using 1 <;> ring
  have hpeak : peak p m ≤ p.ε * p.L1 / 2 * Real.exp (((m : ℝ) - 1) / Real.sqrt m) := by
    unfold peak GapCalibratedWeights.peak
    exact mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
  have hh := AdaptiveTransientParameters.peak_suppression m hm p.L0 p.L1 p.R p.ε
    hp.1 h1 hp.2.2.1 hp.2.2.2.2.1 hmq hq
  have hm' := mul_le_mul_of_nonneg_right hpeak
    (show 0 ≤ (1 / 2 : ℝ) ^ degree p * p.L1 by positivity)
  change _ ≤ p.L0 at hh
  unfold degree scale at hm' ⊢
  nlinarith only [hm', hh]

lemma width_pos (p : Params) (hp : spec.valid p) : 0 < width p := by
  have hR := hp.2.2.1
  unfold width
  positivity

lemma peak_pos (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) (hq : 1 ≤ scale p) :
    0 < peak p m := by
  have h1 := L1_pos p hp hq
  have hε := hp.2.2.2.1
  have ht := spacing_pos p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  unfold peak slope GapCalibratedWeights.peak
  positivity

lemma coefficient_tuning (p : Params) (hp : spec.valid p) (m : ℕ) :
    coefficient p m * width p = peak p m + p.L0 * width p / 1000 := by
  have hB := (width_pos p hp).ne'
  unfold coefficient
  field_simp

lemma slope_bound (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) (hq : 1 ≤ scale p) :
    slope p m ≤ p.ε * p.L1 := by
  have h1 := L1_pos p hp hq
  have hε := hp.2.2.2.1
  have hw := logarithm_ge_one p hp
  have hw0 : 0 < logarithm p := by linarith
  have ht1 := spacing_le_one p hp hm
  have hr : spacing p m / (25 * logarithm p) ≤ 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ p.ε * (p.L1 / 4) by positivity)
  unfold slope
  convert hh using 1 <;> ring

lemma peak_log (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) (hq : 1 ≤ scale p) :
    Real.log (1 + (p.L1 / 4) * peak p m / (p.L0 / 4)) ≤
      2 * logarithm p + (m : ℝ) * spacing p m := by
  have h1 := L1_pos p hp hq
  have h0 := hp.1
  have hε := hp.2.2.2.1
  have ht := spacing_pos p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  have hg : 0 < slope p m := by unfold slope; positivity
  have hr : (p.L1 / 4) * slope p m / (p.L0 / 4) ≤ scale p ^ 2 := by
    rw [show (p.L1 / 4) * slope p m / (p.L0 / 4) = p.L1 * slope p m / p.L0 by ring]
    apply (div_le_iff₀ h0).mpr
    have hcoef := mul_le_mul_of_nonneg_left (slope_bound p hp hm hq) h1.le
    have hεu := mul_le_mul_of_nonneg_right hp.2.2.2.2.1 (sq_nonneg p.L1)
    dsimp [scale]
    nlinarith [mul_nonneg h0.le (sq_nonneg (p.L1 * p.R))]
  have hlog : Real.log (1 + scale p) ≤ logarithm p := by
    have hh := Real.log_le_log (by linarith : 0 < 1 + scale p)
      (show 1 + scale p ≤ 2 + scale p by linarith)
    unfold logarithm
    linarith
  exact GapCalibratedParameters.log_peak_bound m (p.L0 / 4) (p.L1 / 4) (slope p m)
    (spacing p m) (scale p) (logarithm p) (by positivity) (by positivity) hg ht.le
    (by linarith) hr hlog

lemma entropy_log (p : Params) {m : ℕ} (hm : 0 < m)
    (hmq : (m : ℝ) ≤ scale p) : Real.log (1 + Real.sqrt m) ≤ logarithm p := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : Real.sqrt m ≤ m := by nlinarith [Real.sq_sqrt hm0, Real.sqrt_nonneg (m : ℝ)]
  have hh := Real.log_le_log (show 0 < 1 + Real.sqrt m by positivity)
    (show 1 + Real.sqrt m ≤ 2 + scale p by linarith)
  unfold logarithm
  linarith

lemma threshold_pos (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) (hq : 1 ≤ scale p) :
    0 < threshold p m := by
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  unfold threshold
  positivity

lemma hiding_ratio (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m) (hq : 1 ≤ scale p) :
    (4 * width p) ^ 2 / threshold p m ^ 2 ≤
      18014398509481984 * scale p ^ 2 * (m : ℝ) ^ 2 := by
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htl := spacing_lower p hp hm
  have hmul := (div_le_iff₀ (by positivity : 0 < 4 * (m : ℝ))).mp htl
  have hratio : 4 * width p / threshold p m ≤ 134217728 * scale p * (m : ℝ) := by
    have he : 4 * width p / threshold p m = 33554432 * scale p / spacing p m := by
      unfold width threshold scale
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 33554432 * scale p by linarith)
    nlinarith only [hh]
  have hs := pow_le_pow_left₀ (show 0 ≤ 4 * width p / threshold p m by
    have hB := width_pos p hp
    have hθ := threshold_pos p hp hm hq
    positivity) hratio 2
  rw [div_pow] at hs
  nlinarith only [hs]

lemma hiding_dimension (p : Params) (hp : spec.valid p) {m : ℕ} (hm : 0 < m)
    (hq : 1 ≤ scale p) (hmq : (m : ℝ) ≤ scale p) :
    2 * (m : ℝ) ^ 2 * ((4 * width p) ^ 2 / threshold p m ^ 2) + (m : ℝ) ≤ p.d := by
  let U := 1 + scale p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)
  have hU : 1 ≤ U := by dsimp [U]; linarith [Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)]
  have hqU : scale p ≤ U := by dsimp [U]; linarith [Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)]
  have hmU : (m : ℝ) ≤ U := hmq.trans hqU
  have hr := mul_le_mul_of_nonneg_left (hiding_ratio p hp hm hq) (show 0 ≤ 2 * (m : ℝ) ^ 2 by positivity)
  have hm4 := pow_le_pow_left₀ (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hmU 4
  have hq2 := pow_le_pow_left₀ (show 0 ≤ scale p by linarith) hqU 2
  have hprod := mul_le_mul hq2 hm4 (pow_nonneg (Nat.cast_nonneg m) 4) (sq_nonneg U)
  have h6 : U ^ 6 ≤ U ^ 10 := pow_le_pow_right₀ hU (by norm_num)
  have h1 : U ≤ U ^ 10 := by simpa using pow_le_pow_right₀ hU (show 1 ≤ 10 by norm_num)
  have hdim := Nat.le_ceil (1208925819614629174706176 * U ^ 10)
  have hpdim : (⌈1208925819614629174706176 * U ^ 10⌉₊ : ℝ) ≤ p.d := by
    exact_mod_cast hp.2.2.2.2.2.2
  have hpow : 0 ≤ U ^ 10 := by positivity
  nlinarith only [hr, hprod, h6, h1, hmU, hdim, hpdim, hpow]

end LongTails.Proofs.GapTransientParameters
