import LongTails.Proofs.DashaScalingParameters
import LongTails.Algorithms.DashaDistributedSelection
import Mathlib.Data.Nat.Size

namespace LongTails.Proofs.DashaPrecisionCutoff

noncomputable def factor (w : ℝ) : ℝ := Real.sqrt (w * (2 * w + 1))

lemma factor_nonneg (w : ℝ) : 0 ≤ factor w := Real.sqrt_nonneg _

lemma factor_sq {w : ℝ} (hw : 0 ≤ w) : factor w ^ 2 = w * (2 * w + 1) := by
  apply Real.sq_sqrt
  positivity

lemma factor_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : factor x ≤ factor y := by
  apply Real.sqrt_le_sqrt
  nlinarith

lemma factor_product {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * x * y ≤ factor x * factor y := by
  apply (sq_le_sq₀ (by positivity) (mul_nonneg (factor_nonneg x) (factor_nonneg y))).mp
  simp only [mul_pow, factor_sq hx, factor_sq hy]
  have h : 0 ≤ x * y * (2 * x + 2 * y + 1) := by positivity
  nlinarith only [h]

lemma factor_subadd {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    factor (x + y) ≤ factor x + factor y := by
  apply (sq_le_sq₀ (factor_nonneg _) (add_nonneg (factor_nonneg _) (factor_nonneg _))).mp
  have hxy := factor_product hx hy
  nlinarith only [factor_sq hx, factor_sq hy, factor_sq (add_nonneg hx hy), hxy]

lemma factor_scale {c x : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) :
    factor (c * x) ≤ c * factor x := by
  have hc0 : 0 ≤ c := by linarith
  apply (sq_le_sq₀ (factor_nonneg _) (mul_nonneg hc0 (factor_nonneg _))).mp
  rw [mul_pow, factor_sq hx, factor_sq (mul_nonneg hc0 hx)]
  have h : 0 ≤ c * (c - 1) * x := by positivity
  nlinarith only [h]

lemma cutoff_rate {L β u α w : ℝ} (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 8) (huw : u ≤ w)
    (hfloor : β * factor α ≤ L / 4) :
    L + β * factor ((1 + α) * u + α) ≤ (5 / 4) * (L + β * factor w) := by
  have hscaled := factor_scale (show 1 ≤ 1 + α by linarith) hu
  have hsum := factor_subadd (mul_nonneg (show 0 ≤ 1 + α by linarith) hu) hα
  have hm := factor_mono hu huw
  have ha := mul_le_mul_of_nonneg_right hαmax (factor_nonneg u)
  have hscaleβ := mul_le_mul_of_nonneg_left hscaled hβ
  have hsumβ := mul_le_mul_of_nonneg_left hsum hβ
  have hmβ := mul_le_mul_of_nonneg_left hm hβ
  have haβ := mul_le_mul_of_nonneg_left ha hβ
  have hw0 := mul_nonneg hβ (factor_nonneg w)
  nlinarith only [hfloor, hscaleβ, hsumβ, hmβ, haβ, hw0]

lemma cutoff_tracking_weight {u α w : ℝ} (hu : 0 ≤ u)
    (hαmax : α ≤ 1 / 8) (huw : u ≤ w) :
    4 * ((1 + α) * u + α) + 1 ≤ (3 / 2) * (4 * w + 1) := by
  have ha := mul_le_mul_of_nonneg_right hαmax hu
  nlinarith

lemma cutoff_rounds {N Nnew : ℝ} (hnew : Nnew ≤ (27 / 16) * N + 1 / 4) :
    1 + ⌈Nnew⌉₊ ≤ 2 * (1 + ⌈N⌉₊) := by
  have hm := Nat.le_ceil N
  have hb : Nnew ≤ ((2 * ⌈N⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hc := Nat.ceil_le.mpr hb
  omega

noncomputable def roundingNoise (r : ℕ) : ℝ := 2 / 4 ^ r

lemma roundingNoise_nonneg (r : ℕ) : 0 ≤ roundingNoise r := by unfold roundingNoise; positivity

lemma cap_power (x : ℝ) : 4 * x ≤ (2 : ℝ) ^ (2 + Nat.size ⌈x⌉₊) := by
  have hc : (⌈x⌉₊ : ℝ) ≤ (2 : ℝ) ^ Nat.size ⌈x⌉₊ := by exact_mod_cast (Nat.lt_size_self ⌈x⌉₊).le
  calc
    _ ≤ 4 * (⌈x⌉₊ : ℝ) := mul_le_mul_of_nonneg_left (Nat.le_ceil x) (by norm_num)
    _ ≤ 4 * (2 : ℝ) ^ Nat.size ⌈x⌉₊ := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by rw [pow_add]; norm_num

lemma roundingNoise_le_eighth {r : ℕ} (hr : 2 ≤ r) : roundingNoise r ≤ 1 / 8 := by
  have hp : (16 : ℝ) ≤ 4 ^ r := by
    calc
      _ = (4 : ℝ) ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hr
  have hb := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) < 16 by norm_num) hp
  norm_num at hb
  exact hb

lemma power_four (r : ℕ) : (4 : ℝ) ^ r = ((2 : ℝ) ^ r) ^ 2 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

lemma factor_noise_le {r : ℕ} (hr : 2 ≤ r) : factor (roundingNoise r) ≤ 2 / (2 : ℝ) ^ r := by
  have hα := roundingNoise_nonneg r
  have hαmax := roundingNoise_le_eighth hr
  have he : (2 / (2 : ℝ) ^ r) ^ 2 = 2 * roundingNoise r := by
    unfold roundingNoise
    rw [div_pow, power_four]
    ring
  apply (sq_le_sq₀ (factor_nonneg _) (by positivity)).mp
  rw [factor_sq hα, he]
  nlinarith

lemma cap_factor {L β : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) :
    β * factor (roundingNoise (2 + Nat.size ⌈2 * β / L⌉₊)) ≤ L / 4 := by
  have hp := cap_power (2 * β / L)
  have hd : 8 * β / L ≤ (2 : ℝ) ^ (2 + Nat.size ⌈2 * β / L⌉₊) := by
    convert hp using 1
    ring
  have hm := (div_le_iff₀ hL).mp hd
  calc
    _ ≤ β * (2 / (2 : ℝ) ^ (2 + Nat.size ⌈2 * β / L⌉₊)) :=
      mul_le_mul_of_nonneg_left (factor_noise_le (by omega)) hβ
    _ = 2 * β / (2 : ℝ) ^ (2 + Nat.size ⌈2 * β / L⌉₊) := by ring
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hm])

lemma cap_noise_weight {t z ε : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) (hε : 0 < ε) :
    t * roundingNoise (2 + Nat.size ⌈Real.sqrt (2 * t) * z / ε⌉₊) * z ^ 2 ≤ ε ^ 2 / 16 := by
  let R := 2 + Nat.size ⌈Real.sqrt (2 * t) * z / ε⌉₊
  let P : ℝ := 2 ^ R
  have hp : 0 < P := by dsimp [P]; positivity
  have hb := cap_power (Real.sqrt (2 * t) * z / ε)
  have hd : 4 * Real.sqrt (2 * t) * z / ε ≤ P := by
    convert hb using 1
    ring
  have hm := (div_le_iff₀ hε).mp hd
  have hsq : (4 * Real.sqrt (2 * t) * z) ^ 2 ≤ (P * ε) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hm
  have hs : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
  simp only [mul_pow, hs] at hsq
  change t * (2 / (4 : ℝ) ^ R) * z ^ 2 ≤ _
  rw [power_four]
  change t * (2 / P ^ 2) * z ^ 2 ≤ _
  have he : t * (2 / P ^ 2) * z ^ 2 = 2 * t * z ^ 2 / P ^ 2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith only [hsq]

lemma variance_cap_le {u α w : ℝ} (hu : 0 ≤ u) (hαmax : α ≤ 1 / 8) (huw : u ≤ w) :
    (1 + α) * u + α ≤ (9 / 8) * w + α := by
  have ha := mul_le_mul_of_nonneg_right hαmax hu
  nlinarith

lemma penalty_cap_le {t tnew w wnew α z ε : ℝ}
    (htnew : 0 ≤ tnew) (hw : 0 ≤ w) (ht : tnew ≤ (3 / 2) * t)
    (hnew : wnew ≤ (9 / 8) * w + α)
    (hfloor : tnew * α * z ^ 2 ≤ ε ^ 2 / 16) :
    tnew * wnew * z ^ 2 ≤ (27 / 16) * (t * w * z ^ 2) + ε ^ 2 / 16 := by
  have ha := mul_le_mul_of_nonneg_left hnew htnew
  have hb := mul_le_mul_of_nonneg_right ht (show 0 ≤ (9 / 8 : ℝ) * w by positivity)
  have hc := mul_le_mul_of_nonneg_right ha (sq_nonneg z)
  have hd := mul_le_mul_of_nonneg_right hb (sq_nonneg z)
  nlinarith only [hc, hd, hfloor]

lemma capped_rate {L β u w : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (hu : 0 ≤ u) (huw : u ≤ w) :
    L + β * factor ((1 + roundingNoise (2 + Nat.size ⌈2 * β / L⌉₊)) * u +
      roundingNoise (2 + Nat.size ⌈2 * β / L⌉₊)) ≤ (5 / 4) * (L + β * factor w) :=
  cutoff_rate hβ hu (roundingNoise_nonneg _) (roundingNoise_le_eighth (by omega)) huw (cap_factor hL hβ)

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Algorithms.DashaDistributedSelection

variable {p : Params}

lemma denominator_factor (c : Choice p) :
    denominator p c = min p.L p.Lhat + (p.Lhat / Real.sqrt (p.n : ℝ)) * factor (variance p c) := by
  unfold denominator factor
  rw [Real.sqrt_div' _ (by positivity)]
  ring

lemma multiplier_sub_one_le_variance (c : Choice p) :
    LongTails.Algorithms.DashaCyclic.multiplier c.block - 1 ≤ variance p c := by
  have hq := DashaScalingParameters.multiplier_ge_one c
  have hα : 0 ≤ 2 / (4 : ℝ) ^ c.precision := by positivity
  unfold variance
  nlinarith

lemma mainPrecision_eq (p : Params) :
    mainPrecision p = 2 + Nat.size ⌈2 * (p.Lhat / Real.sqrt (p.n : ℝ)) / min p.L p.Lhat⌉₊ := by
  unfold mainPrecision
  congr 3
  ring

lemma capChoice_denominator (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    denominator p (capChoice p c) ≤ (5 / 4) * denominator p c := by
  by_cases hc : c.precision ≤ mainPrecision p
  · have he : capChoice p c = c := by cases c; simp_all [capChoice]
    rw [he]
    have hd := DashaScalingParameters.denominator_pos c hL hH
    linarith
  · have hr : min c.precision (mainPrecision p) = mainPrecision p := min_eq_right (le_of_not_ge hc)
    let u := LongTails.Algorithms.DashaCyclic.multiplier c.block - 1
    have hu : 0 ≤ u := sub_nonneg.mpr (DashaScalingParameters.multiplier_ge_one c)
    have hb := capped_rate (lt_min hL hH) (show 0 ≤ p.Lhat / Real.sqrt (p.n : ℝ) by positivity)
      hu (multiplier_sub_one_le_variance c)
    have hw : variance p (capChoice p c) =
        (1 + roundingNoise (mainPrecision p)) * u + roundingNoise (mainPrecision p) := by
      unfold variance capChoice roundingNoise
      rw [hr]
      dsimp [u]
      ring
    rw [denominator_factor, denominator_factor, hw, mainPrecision_eq]
    exact hb

lemma capChoice_tracking_weight (c : Choice p) :
    4 * variance p (capChoice p c) + 1 ≤ (3 / 2) * (4 * variance p c + 1) := by
  by_cases hc : c.precision ≤ mainPrecision p
  · have he : capChoice p c = c := by cases c; simp_all [capChoice]
    rw [he]
    have hw := DashaScalingParameters.variance_nonneg c
    linarith
  · have hr : min c.precision (mainPrecision p) = mainPrecision p := min_eq_right (le_of_not_ge hc)
    let u := LongTails.Algorithms.DashaCyclic.multiplier c.block - 1
    have hu : 0 ≤ u := sub_nonneg.mpr (DashaScalingParameters.multiplier_ge_one c)
    have hR : 2 ≤ mainPrecision p := by unfold mainPrecision; omega
    have hb := cutoff_tracking_weight hu (roundingNoise_le_eighth hR) (multiplier_sub_one_le_variance c)
    have hw : variance p (capChoice p c) =
        (1 + roundingNoise (mainPrecision p)) * u + roundingNoise (mainPrecision p) := by
      unfold variance capChoice roundingNoise
      rw [hr]
      dsimp [u]
      ring
    rw [hw]
    exact hb

lemma initialPrecision_eq (c : Choice p) :
    initialPrecision p c = 2 + Nat.size ⌈Real.sqrt (2 * (4 * variance p c + 1)) *
      (p.G / Real.sqrt (p.n : ℝ)) / p.ε⌉₊ := by
  unfold initialPrecision
  congr 3
  ring

lemma initial_cap_noise (c : Choice p) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (4 * variance p c + 1) * roundingNoise (initialPrecision p c) * p.G ^ 2 / p.n ≤ p.ε ^ 2 / 16 := by
  have hw := DashaScalingParameters.variance_nonneg c
  have hb := cap_noise_weight (show 0 ≤ 4 * variance p c + 1 by positivity)
    (show 0 ≤ p.G / Real.sqrt (p.n : ℝ) by positivity) hε
  rw [← initialPrecision_eq c] at hb
  rw [div_pow, Real.sq_sqrt (by positivity)] at hb
  convert hb using 1
  ring

lemma capInitializer_variance (c initializer : Choice p) :
    variance p (capInitializer p c initializer) ≤ (9 / 8) * variance p initializer +
      roundingNoise (initialPrecision p c) := by
  by_cases hi : initializer.precision ≤ initialPrecision p c
  · have he : capInitializer p c initializer = initializer := by cases initializer; simp_all [capInitializer]
    rw [he]
    have hw := DashaScalingParameters.variance_nonneg initializer
    have hα := roundingNoise_nonneg (initialPrecision p c)
    linarith
  · have hr : min initializer.precision (initialPrecision p c) = initialPrecision p c :=
      min_eq_right (le_of_not_ge hi)
    let u := LongTails.Algorithms.DashaCyclic.multiplier initializer.block - 1
    have hu : 0 ≤ u := sub_nonneg.mpr (DashaScalingParameters.multiplier_ge_one initializer)
    have hR : 2 ≤ initialPrecision p c := by unfold initialPrecision; omega
    have hb := variance_cap_le hu (roundingNoise_le_eighth hR) (multiplier_sub_one_le_variance initializer)
    have hw : variance p (capInitializer p c initializer) =
        (1 + roundingNoise (initialPrecision p c)) * u + roundingNoise (initialPrecision p c) := by
      unfold variance capInitializer roundingNoise
      rw [hr]
      dsimp [u]
      ring
    rw [hw]
    exact hb

lemma cap_penalty (c initializer : Choice p) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    initialPenalty p (capChoice p c) (capInitializer p (capChoice p c) initializer) ≤
      (27 / 16) * initialPenalty p c initializer + p.ε ^ 2 / 16 := by
  have hw := DashaScalingParameters.variance_nonneg (capChoice p c)
  have hz : (p.G / Real.sqrt (p.n : ℝ)) ^ 2 = p.G ^ 2 / p.n := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hf : (4 * variance p (capChoice p c) + 1) * roundingNoise (initialPrecision p (capChoice p c)) *
      (p.G / Real.sqrt (p.n : ℝ)) ^ 2 ≤ p.ε ^ 2 / 16 := by
    rw [hz]
    convert initial_cap_noise (capChoice p c) hG hε using 1
    ring
  have hb := penalty_cap_le (show 0 ≤ 4 * variance p (capChoice p c) + 1 by positivity)
    (DashaScalingParameters.variance_nonneg initializer) (capChoice_tracking_weight c)
    (capInitializer_variance (capChoice p c) initializer) hf
  rw [hz] at hb
  unfold initialPenalty
  convert hb using 1 <;> ring

lemma cap_iterations (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    (iterations p (capChoice p c) : ℕ) ≤ 2 * (iterations p c : ℕ) := by
  have hD := capChoice_denominator c hL hH
  have hD0 := DashaScalingParameters.denominator_pos c hL hH
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD (show 0 ≤ 32 * p.Δ by positivity)) (sq_nonneg p.ε)
  have he : 32 * p.Δ * ((5 / 4) * denominator p c) / p.ε ^ 2 =
      (5 / 4) * (32 * p.Δ * denominator p c / p.ε ^ 2) := by ring
  rw [he] at hb
  have hN : 0 ≤ 32 * p.Δ * denominator p c / p.ε ^ 2 := by positivity
  exact cutoff_rounds (by linarith only [hb, hN])

lemma cap_sparseIterations (c initializer : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (sparseIterations p (capChoice p c) (capInitializer p (capChoice p c) initializer) : ℕ) ≤
      2 * (sparseIterations p c initializer : ℕ) := by
  have hD := capChoice_denominator c hL hH
  have hA := cap_penalty c initializer hG hε
  have hD0 := DashaScalingParameters.denominator_pos c hL hH
  have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ 32 * p.Δ by positivity)
  have hpos : 0 ≤ p.Δ * denominator p c := by positivity
  have hb : 32 * p.Δ * denominator p (capChoice p c) +
      4 * initialPenalty p (capChoice p c) (capInitializer p (capChoice p c) initializer) ≤
      (27 / 16) * (32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) + p.ε ^ 2 / 4 := by
    nlinarith only [hm, hA, hpos]
  have hd := div_le_div_of_nonneg_right hb (sq_nonneg p.ε)
  have he : ((27 / 16) * (32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) + p.ε ^ 2 / 4) / p.ε ^ 2 =
      (27 / 16) * ((32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2) + 1 / 4 := by
    field_simp [ne_of_gt hε]
  rw [he] at hd
  exact cutoff_rounds hd

lemma roundingNoise_antitone : Antitone roundingNoise := by
  intro r s hrs
  unfold roundingNoise
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ (by norm_num) hrs)

lemma capChoice_variance_ge (c : Choice p) : variance p c ≤ variance p (capChoice p c) := by
  have hα := roundingNoise_antitone (Nat.min_le_left c.precision (mainPrecision p))
  have hq := DashaScalingParameters.multiplier_ge_one c
  unfold variance capChoice roundingNoise at *
  nlinarith

lemma capChoice_variance_ratio (c : Choice p) :
    variance p (capChoice p c) + 1 ≤ (9 / 8) * (variance p c + 1) := by
  by_cases hc : c.precision ≤ mainPrecision p
  · have he : capChoice p c = c := by cases c; simp_all [capChoice]
    rw [he]
    have hw := DashaScalingParameters.variance_nonneg c
    linarith
  · have hr : min c.precision (mainPrecision p) = mainPrecision p := min_eq_right (le_of_not_ge hc)
    have hR : 2 ≤ mainPrecision p := by unfold mainPrecision; omega
    have hα := roundingNoise_le_eighth hR
    have hα0 := roundingNoise_nonneg c.precision
    have hq := DashaScalingParameters.multiplier_ge_one c
    have h1 := mul_le_mul_of_nonneg_right hα (show 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block by linarith)
    have h2 := mul_nonneg hα0 (show 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block by linarith)
    unfold variance capChoice
    rw [hr]
    unfold roundingNoise at h1 h2
    nlinarith only [h1, h2]

lemma capChoice_denominator_ge (c : Choice p) (hH : 0 ≤ p.Lhat) :
    denominator p c ≤ denominator p (capChoice p c) := by
  rw [denominator_factor, denominator_factor]
  have hm := mul_le_mul_of_nonneg_left
    (factor_mono (DashaScalingParameters.variance_nonneg c) (capChoice_variance_ge c))
    (show 0 ≤ p.Lhat / Real.sqrt (p.n : ℝ) by positivity)
  exact add_le_add le_rfl hm

lemma capChoice_stepSize_le (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    stepSize p (capChoice p c) ≤ stepSize p c := by
  have hp := DashaScalingParameters.denominator_pos c hL hH
  unfold stepSize
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (mul_le_mul_of_nonneg_left (capChoice_denominator_ge c hH.le) (by norm_num))

lemma spacing_square_identity (c : Choice p) :
    spacing p c ^ 2 * (variance p c + 1) = p.ε ^ 2 * (p.n : ℝ) / (256 * p.d) := by
  have hw := DashaScalingParameters.variance_nonneg c
  rw [DashaScalingParameters.spacing_sq]
  field_simp

lemma capChoice_spacing_le (c : Choice p) (hε : 0 < p.ε) :
    spacing p (capChoice p c) ≤ spacing p c := by
  have hp := DashaScalingParameters.spacing_pos c hε
  have hn := DashaScalingParameters.spacing_pos (capChoice p c) hε
  have hw := DashaScalingParameters.variance_nonneg c
  have hm := mul_le_mul_of_nonneg_left (capChoice_variance_ge c) (sq_nonneg (spacing p (capChoice p c)))
  have ho := spacing_square_identity c
  have hnew := spacing_square_identity (capChoice p c)
  have hs : (variance p c + 1) * spacing p (capChoice p c) ^ 2 ≤
      (variance p c + 1) * spacing p c ^ 2 := by nlinarith only [hm, ho, hnew]
  have hsq := (mul_le_mul_iff_right₀ (show 0 < variance p c + 1 by positivity)).mp hs
  exact (sq_le_sq₀ hn.le hp.le).mp hsq

lemma capChoice_spacing_ratio (c : Choice p) (hε : 0 < p.ε) :
    spacing p c ≤ 2 * spacing p (capChoice p c) := by
  have hp := DashaScalingParameters.spacing_pos c hε
  have hn := DashaScalingParameters.spacing_pos (capChoice p c) hε
  have hw := DashaScalingParameters.variance_nonneg c
  have hratio : variance p (capChoice p c) + 1 ≤ 4 * (variance p c + 1) := by
    linarith [capChoice_variance_ratio c]
  have hm := mul_le_mul_of_nonneg_left hratio (sq_nonneg (spacing p (capChoice p c)))
  have ho := spacing_square_identity c
  have hnew := spacing_square_identity (capChoice p c)
  have hs : (variance p c + 1) * spacing p c ^ 2 ≤
      (variance p c + 1) * (4 * spacing p (capChoice p c) ^ 2) := by nlinarith only [hm, ho, hnew]
  have hsq := (mul_le_mul_iff_right₀ (show 0 < variance p c + 1 by positivity)).mp hs
  apply (sq_le_sq₀ hp.le (by positivity)).mp
  nlinarith only [hsq]

lemma variance_factor_sandwich {q α : ℝ} (hq : 1 ≤ q) (hα : 0 ≤ α) (hα2 : α ≤ 2) :
    q * (q - 1) + α * q ^ 2 ≤ factor ((1 + α) * q - 1) ^ 2 ∧
    factor ((1 + α) * q - 1) ^ 2 ≤ 6 * (q * (q - 1) + α * q ^ 2) := by
  have hq0 : 0 ≤ q := by linarith
  have ha0 := mul_nonneg hα hq0
  have ha2 := mul_le_mul_of_nonneg_right hα2 hq0
  have hw : 0 ≤ (1 + α) * q - 1 := by nlinarith
  rw [factor_sq hw]
  have hlo : q ≤ 2 * ((1 + α) * q - 1) + 1 := by nlinarith
  have hhi : 2 * ((1 + α) * q - 1) + 1 ≤ 6 * q := by nlinarith
  constructor
  · have hm := mul_le_mul_of_nonneg_left hlo hw
    nlinarith only [hm]
  · have hm := mul_le_mul_of_nonneg_left hhi hw
    nlinarith only [hm]

lemma variance_weight_sandwich {q α : ℝ} (hq : 1 ≤ q) (hα : 0 ≤ α) (hα2 : α ≤ 2) :
    q ≤ 4 * ((1 + α) * q - 1) + 1 ∧ 4 * ((1 + α) * q - 1) + 1 ≤ 12 * q := by
  have hq0 : 0 ≤ q := by linarith
  have ha0 := mul_nonneg hα hq0
  have ha2 := mul_le_mul_of_nonneg_right hα2 hq0
  constructor <;> nlinarith

end LongTails.Proofs.DashaPrecisionCutoff
