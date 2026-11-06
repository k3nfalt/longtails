import LongTails.Proofs.HystereticHessianParameters

namespace LongTails.Proofs.HystereticHessianBudget

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianParameters

lemma rounded_batch_upper {x : ℝ} (hx : 1 ≤ x) :
    (⌈x⌉₊ + 1 : ℕ) ≤ 3 * x := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  push_cast
  linarith

lemma rounded_epoch_bounds {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hpos : 1 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hx
  have hlt := Nat.lt_floor_add_one x
  exact ⟨by linarith, Nat.floor_le (by linarith)⟩

lemma epoch_bounds (p : Params) (hv : spec.valid p) :
    min ((noiseLevel p) ^ (tailPower p * (p.q - 1) / p.q))
      ((noiseLevel p / relativeNoise p) ^ tailPower p) / 2 ≤ (epochCount p : ℝ) ∧
    (epochCount p : ℝ) ≤ (noiseLevel p) ^ (tailPower p * (p.q - 1) / p.q) ∧
    (epochCount p : ℝ) ≤ (noiseLevel p / relativeNoise p) ^ tailPower p := by
  have hh := rounded_epoch_bounds (epoch_base_one_le p hv)
  exact ⟨hh.1, hh.2.trans (min_le_left _ _), hh.2.trans (min_le_right _ _)⟩

lemma groupCount_upper (p : Params) (hv : spec.valid p) :
    (groupCount p : ℝ) ≤ 4 * confidence p := by
  have hl := confidence_one_le p hv
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * confidence p by linarith)
  dsimp [groupCount]
  push_cast
  linarith

lemma pilotBatchCount_upper (p : Params) (hv : spec.valid p) :
    (pilotBatchCount p : ℝ) ≤ 3 * ((2 : ℝ) ^ 24 * relativeNoise p) ^ tailPower p := by
  apply rounded_batch_upper
  apply Real.one_le_rpow
  · have hh := (noise_scales p hv).1
    norm_num
    linarith
  · linarith [tailPower_two_le p hv]

lemma resetBatchCount_upper (p : Params) (hv : spec.valid p) :
    (resetBatchCount p : ℝ) ≤ 3 * ((2 : ℝ) ^ 24 * noiseLevel p) ^ tailPower p := by
  apply rounded_batch_upper
  apply Real.one_le_rpow
  · have hh := (noise_scales p hv).1.trans (noise_scales p hv).2.1
    norm_num
    linarith
  · linarith [tailPower_two_le p hv]

lemma transportBatchCount_upper (p : Params) (hv : spec.valid p) :
    (transportBatchCount p : ℝ) ≤
      512 * confidence p * (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1)) := by
  have hl := confidence_one_le p hv
  have hm : 1 ≤ (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hp : 1 ≤ (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1)) :=
    Real.one_le_rpow (by linarith) (by positivity)
  have hx : 2 ≤ 256 * confidence p * (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1)) := by
    nlinarith
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 256 * confidence p *
    (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1)) by linarith)
  dsimp [transportBatchCount]
  push_cast
  nlinarith

lemma epoch_pilot_power (p : Params) (hv : spec.valid p) :
    (epochCount p : ℝ) * (relativeNoise p) ^ tailPower p ≤ (noiseLevel p) ^ tailPower p := by
  have hs := noise_scales p hv
  have hA : 0 < relativeNoise p := by linarith [hs.1]
  have hS : 0 ≤ noiseLevel p := by linarith [hs.1, hs.2.1]
  have hh := mul_le_mul_of_nonneg_right (epoch_bounds p hv).2.2
    (Real.rpow_nonneg hA.le (tailPower p))
  rw [Real.div_rpow hS hA.le, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hA _))] at hh
  exact hh

lemma epoch_transport_power (p : Params) (hv : spec.valid p) :
    (epochCount p : ℝ) ^ (p.q / (p.q - 1)) ≤ (noiseLevel p) ^ tailPower p := by
  have hs := noise_scales p hv
  have hS : 0 ≤ noiseLevel p := by linarith [hs.1, hs.2.1]
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg (epochCount p)) (epoch_bounds p hv).2.1
    (show 0 ≤ p.q / (p.q - 1) by positivity)
  rw [← Real.rpow_mul hS] at hh
  have hid : tailPower p * (p.q - 1) / p.q * (p.q / (p.q - 1)) = tailPower p := by
    field_simp [ne_of_gt (show 0 < p.q by linarith), ne_of_gt (show 0 < p.q - 1 by linarith)]
  rwa [hid] at hh

lemma epoch_le_noise_power (p : Params) (hv : spec.valid p) :
    (epochCount p : ℝ) ≤ (noiseLevel p) ^ tailPower p := by
  have hs := noise_scales p hv
  have hAp := Real.one_le_rpow hs.1 (show 0 ≤ tailPower p by linarith [tailPower_two_le p hv])
  calc
    (epochCount p : ℝ) ≤ (epochCount p : ℝ) * (relativeNoise p) ^ tailPower p := by
      nlinarith [show (0 : ℝ) ≤ (epochCount p : ℝ) from Nat.cast_nonneg _]
    _ ≤ _ := epoch_pilot_power p hv

lemma relative_power_absorption (p : Params) (hv : spec.valid p) :
    (relativeNoise p) ^ tailPower p ≤ (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2) := by
  have hs := noise_scales p hv
  have hA : 0 < relativeNoise p := by linarith [hs.1]
  have hh := Real.rpow_le_rpow hA.le hs.2.1
    (show 0 ≤ tailPower p - 2 by linarith [tailPower_two_le p hv])
  calc
    (relativeNoise p) ^ tailPower p = (relativeNoise p) ^ 2 * (relativeNoise p) ^ (tailPower p - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_add hA]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (sq_nonneg _)

lemma macroCalls_upper (p : Params) (hv : spec.valid p) :
    (macroCalls (tunedConfig p) : ℝ) ≤
      (36 * ((2 : ℝ) ^ 24) ^ tailPower p + 512 * (256 : ℝ) ^ (1 / (p.q - 1))) *
        confidence p * (noiseLevel p) ^ tailPower p := by
  have hs := noise_scales p hv
  have hA : 0 ≤ relativeNoise p := by linarith [hs.1]
  have hS : 0 ≤ noiseLevel p := hA.trans hs.2.1
  have hl : 0 ≤ confidence p := by linarith [confidence_one_le p hv]
  have hm : 1 ≤ (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hpilot := pilotBatchCount_upper p hv
  have hreset := resetBatchCount_upper p hv
  rw [Real.mul_rpow (by positivity) hA] at hpilot
  rw [Real.mul_rpow (by positivity) hS] at hreset
  have hpilotcall := mul_le_mul (groupCount_upper p hv) hpilot
    (Nat.cast_nonneg _) (by positivity : 0 ≤ 4 * confidence p)
  have hresetcall := mul_le_mul (groupCount_upper p hv) hreset
    (Nat.cast_nonneg _) (by positivity : 0 ≤ 4 * confidence p)
  have hpilotepoch := mul_le_mul_of_nonneg_left (epoch_pilot_power p hv)
    (show 0 ≤ 24 * confidence p * ((2 : ℝ) ^ 24) ^ tailPower p by positivity)
  have hpilotall := mul_le_mul_of_nonneg_left hpilotcall
    (show 0 ≤ (epochCount p : ℝ) + 1 by positivity)
  have hpilotdouble := mul_le_mul_of_nonneg_right (show (epochCount p : ℝ) + 1 ≤ 2 * epochCount p by linarith)
    (show 0 ≤ 4 * confidence p * (3 * (((2 : ℝ) ^ 24) ^ tailPower p * (relativeNoise p) ^ tailPower p)) by positivity)
  have ht := transportBatchCount_upper p hv
  rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)] at ht
  have htall := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (epochCount p))
  have htid : (epochCount p : ℝ) * (epochCount p : ℝ) ^ (1 / (p.q - 1)) =
      (epochCount p : ℝ) ^ (p.q / (p.q - 1)) := by
    conv_lhs => lhs; rw [← Real.rpow_one (epochCount p : ℝ)]
    rw [← Real.rpow_add (show 0 < (epochCount p : ℝ) by linarith)]
    congr 1
    field_simp [ne_of_gt (show 0 < p.q by linarith), ne_of_gt (show 0 < p.q - 1 by linarith)]
    ring
  have htpow := mul_le_mul_of_nonneg_left (epoch_transport_power p hv)
    (show 0 ≤ 512 * confidence p * (256 : ℝ) ^ (1 / (p.q - 1)) by positivity)
  rw [← htid] at htpow
  have hepoch : (tunedConfig p).epoch + 2 = epochCount p + 1 := by
    have hh := tuned_epoch p hv
    omega
  simp only [macroCalls, resetCalls, pilotCalls, hepoch, tuned_epoch p hv,
    tuned_groups, tuned_resetBatch, tuned_pilotBatch, tuned_transportBatch, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hpbound := hpilotall.trans (hpilotdouble.trans (show
      2 * (epochCount p : ℝ) * (4 * confidence p * (3 * (((2 : ℝ) ^ 24) ^ tailPower p * (relativeNoise p) ^ tailPower p))) ≤
      24 * confidence p * ((2 : ℝ) ^ 24) ^ tailPower p * (noiseLevel p) ^ tailPower p by
    convert hpilotepoch using 1; ring))
  have htbound := htall.trans (show
      (epochCount p : ℝ) * (512 * confidence p * ((256 : ℝ) ^ (1 / (p.q - 1)) * (epochCount p : ℝ) ^ (1 / (p.q - 1)))) ≤
      512 * confidence p * (256 : ℝ) ^ (1 / (p.q - 1)) * (noiseLevel p) ^ tailPower p by
    convert htpow using 1; ring)
  convert add_le_add (add_le_add hresetcall hpbound) htbound using 1; ring

lemma epoch_inverse_bound (p : Params) (hv : spec.valid p) :
    (noiseLevel p) ^ tailPower p / (epochCount p : ℝ) ≤
      2 * ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ tailPower p) := by
  have hs := noise_scales p hv
  have hA : 0 < relativeNoise p := by linarith [hs.1]
  have hS : 0 < noiseLevel p := hA.trans_le hs.2.1
  have hm : 0 < (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have he := (epoch_bounds p hv).1
  have hsplit : tailPower p * (p.q - 1) / p.q + tailPower p / p.q = tailPower p := by
    field_simp
    ring
  have hprod : (noiseLevel p) ^ (tailPower p * (p.q - 1) / p.q) *
      (noiseLevel p) ^ (tailPower p / p.q) = (noiseLevel p) ^ tailPower p := by
    rw [← Real.rpow_add hS, hsplit]
  have hratio : (noiseLevel p / relativeNoise p) ^ tailPower p * (relativeNoise p) ^ tailPower p =
      (noiseLevel p) ^ tailPower p := by
    rw [Real.div_rpow hS.le hA.le, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hA _))]
  apply (div_le_iff₀ hm).mpr
  rcases le_total ((noiseLevel p) ^ (tailPower p * (p.q - 1) / p.q))
    ((noiseLevel p / relativeNoise p) ^ tailPower p) with hh | hh
  · rw [min_eq_left hh] at he
    have ht := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hS.le (tailPower p / p.q))
    have ha := mul_nonneg hm.le (Real.rpow_nonneg hA.le (tailPower p))
    nlinarith only [ht, ha, hprod]
  · rw [min_eq_right hh] at he
    have ht := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hA.le (tailPower p))
    have ha := mul_nonneg hm.le (Real.rpow_nonneg hS.le (tailPower p / p.q))
    nlinarith only [ht, ha, hratio]

lemma localScale_nonneg (p : Params) (hv : spec.valid p) : 0 ≤ localScale p := by
  have hU := (localRadius_pos p hv).le
  rcases hv with ⟨hL0, hL1, _, _, hσh, hαh, _, _, _, _, _, _⟩
  unfold localScale
  positivity

lemma macroCount_upper (p : Params) (hv : spec.valid p) :
    (macroCount p : ℝ) ≤ 8388608 * p.Δ * localScale p / ((targetAccuracy p) ^ 2 * (epochCount p : ℝ)) +
      16384 * p.Δ * localScale p / (localRadius p) ^ 2 + 3 := by
  have hH := localScale_nonneg p hv
  have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 8388608 * p.Δ * localScale p /
    ((targetAccuracy p) ^ 2 * (epochCount p : ℝ)) + 16384 * p.Δ * localScale p / (localRadius p) ^ 2 by positivity)
  dsimp [macroCount]
  push_cast
  linarith

lemma logicalBlocks_upper (p : Params) (hv : spec.valid p) :
    (logicalBlocks p : ℝ) ≤ 5 * (macroCount p : ℝ) * (epochCount p : ℝ) := by
  have hm : 1 ≤ (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hh := mul_le_mul_of_nonneg_left (show 2 * (epochCount p : ℝ) + 3 ≤ 5 * epochCount p by linarith)
    (show (0 : ℝ) ≤ (macroCount p : ℝ) from Nat.cast_nonneg _)
  dsimp [logicalBlocks]
  push_cast
  linarith

lemma radius_cost_identity (p : Params) (hv : spec.valid p) :
    (noiseLevel p) ^ tailPower p / (localRadius p) ^ 2 =
      (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2) / (targetAccuracy p) ^ 2 := by
  have hs := noise_scales p hv
  have hA : 0 < relativeNoise p := by linarith [hs.1]
  have hS : 0 < noiseLevel p := hA.trans_le hs.2.1
  have he := targetAccuracy_pos p hv
  have hU := localRadius_pos p hv
  have hpow : (noiseLevel p) ^ tailPower p = (noiseLevel p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add hS]
    congr 1
    ring
  have hsq : (relativeNoise p) ^ 2 * (localRadius p) ^ 2 =
      (targetAccuracy p) ^ 2 * (noiseLevel p) ^ 2 := by
    nlinarith only [sq_nonneg (relativeNoise p * localRadius p - targetAccuracy p * noiseLevel p),
      congrArg (fun x : ℝ => x ^ 2) hs.2.2.2.1]
  rw [hpow]
  apply (div_eq_div_iff (ne_of_gt (sq_pos_of_pos hU)) (ne_of_gt (sq_pos_of_pos he))).mpr
  nlinarith only [congrArg (fun x : ℝ => x * (noiseLevel p) ^ (tailPower p - 2)) hsq]

lemma macro_epoch_upper (p : Params) (hv : spec.valid p) :
    (macroCount p : ℝ) * (epochCount p : ℝ) ≤
      16777216 * (noiseLevel p) ^ tailPower p * (1 + p.Δ * localScale p / (targetAccuracy p) ^ 2) := by
  have he := targetAccuracy_pos p hv
  have hU := localRadius_pos p hv
  have hm : 0 < (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hH := localScale_nonneg p hv
  have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
  have hD : 0 ≤ p.Δ * localScale p / (targetAccuracy p) ^ 2 := by positivity
  have hs := noise_scales p hv
  have hB : 1 ≤ (noiseLevel p) ^ tailPower p :=
    Real.one_le_rpow (hs.1.trans hs.2.1) (by linarith [tailPower_two_le p hv])
  have hU2 : (targetAccuracy p) ^ 2 ≤ (localRadius p) ^ 2 := by nlinarith [hs.2.2.1]
  have hlocal : p.Δ * localScale p / (localRadius p) ^ 2 ≤ p.Δ * localScale p / (targetAccuracy p) ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg hΔ hH) (sq_pos_of_pos he) hU2
  have hJ := mul_le_mul_of_nonneg_right (macroCount_upper p hv) hm.le
  have hid : (8388608 * p.Δ * localScale p / ((targetAccuracy p) ^ 2 * (epochCount p : ℝ)) +
      16384 * p.Δ * localScale p / (localRadius p) ^ 2 + 3) * (epochCount p : ℝ) =
      8388608 * (p.Δ * localScale p / (targetAccuracy p) ^ 2) +
      16384 * (p.Δ * localScale p / (localRadius p) ^ 2) * (epochCount p : ℝ) + 3 * (epochCount p : ℝ) := by
    field_simp
  rw [hid] at hJ
  have hlocalm := mul_le_mul hlocal (epoch_le_noise_power p hv) hm.le hD
  have hDB := mul_le_mul_of_nonneg_left hB hD
  have hBm := epoch_le_noise_power p hv
  nlinarith only [hJ, hlocalm, hDB, hBm, hB, hD]

lemma macro_noise_upper (p : Params) (hv : spec.valid p) :
    (macroCount p : ℝ) * (noiseLevel p) ^ tailPower p ≤
      33554432 * ((noiseLevel p) ^ tailPower p + p.Δ * localScale p / (targetAccuracy p) ^ 2 *
        ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2))) := by
  have he := targetAccuracy_pos p hv
  have hU := localRadius_pos p hv
  have hm : 0 < (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hH := localScale_nonneg p hv
  have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
  have hs := noise_scales p hv
  have hS : 0 ≤ noiseLevel p := by linarith [hs.1, hs.2.1]
  have hB := Real.rpow_nonneg hS (tailPower p)
  have hD : 0 ≤ p.Δ * localScale p / (targetAccuracy p) ^ 2 := by positivity
  have hT : 0 ≤ (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2) := by positivity
  have hV := Real.rpow_nonneg hS (tailPower p / p.q)
  have hJ := mul_le_mul_of_nonneg_right (macroCount_upper p hv) hB
  have hInv := (epoch_inverse_bound p hv).trans (show
      2 * ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ tailPower p) ≤
      2 * ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2)) by
    linarith [relative_power_absorption p hv])
  have hMain := mul_le_mul_of_nonneg_left hInv hD
  have hid : (8388608 * p.Δ * localScale p / ((targetAccuracy p) ^ 2 * (epochCount p : ℝ)) +
      16384 * p.Δ * localScale p / (localRadius p) ^ 2 + 3) * (noiseLevel p) ^ tailPower p =
      8388608 * (p.Δ * localScale p / (targetAccuracy p) ^ 2) * ((noiseLevel p) ^ tailPower p / (epochCount p : ℝ)) +
      16384 * (p.Δ * localScale p) * ((noiseLevel p) ^ tailPower p / (localRadius p) ^ 2) +
      3 * (noiseLevel p) ^ tailPower p := by ring
  rw [hid, radius_cost_identity p hv] at hJ
  have hDT := mul_nonneg hD hT
  have hDV := mul_nonneg hD hV
  ring_nf at hJ hMain hDT hDV ⊢
  linarith only [hJ, hMain, hDT, hDV, hB]

lemma macro_coefficient_upper (p : Params) (hv : spec.valid p) :
    36 * ((2 : ℝ) ^ 24) ^ tailPower p + 512 * (256 : ℝ) ^ (1 / (p.q - 1)) ≤
      (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 16) := by
  have hb : 0 ≤ tailPower p := by linarith [tailPower_two_le p hv]
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hC := Real.one_le_rpow (show (1 : ℝ) ≤ 2 ^ 24 by norm_num) hb
  have hT := Real.one_le_rpow (show (1 : ℝ) ≤ 256 by norm_num) (show 0 ≤ 1 / (p.q - 1) by positivity)
  have hprod1 := mul_le_mul_of_nonneg_left hT (show 0 ≤ ((2 : ℝ) ^ 24) ^ tailPower p by positivity)
  have hprod2 := mul_le_mul_of_nonneg_right hC (show 0 ≤ (256 : ℝ) ^ (1 / (p.q - 1)) by positivity)
  have hid : (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 16) =
      65536 * (((2 : ℝ) ^ 24) ^ tailPower p) * (256 : ℝ) ^ (1 / (p.q - 1)) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hh : (2 : ℝ) ^ (8 / (p.q - 1)) = (256 : ℝ) ^ (1 / (p.q - 1)) := by
      rw [show 8 / (p.q - 1) = 8 * (1 / (p.q - 1)) by ring, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hh]
    norm_num
    ring
  rw [hid]
  nlinarith only [hC, hT, hprod1, hprod2]

lemma trialCalls_upper (p : Params) (hv : spec.valid p) :
    (trialCalls (tunedConfig p) : ℝ) ≤
      (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 41) * confidence p *
        ((noiseLevel p) ^ tailPower p + p.Δ * localScale p / (targetAccuracy p) ^ 2 *
          ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2))) := by
  have hs := noise_scales p hv
  have hS : 0 ≤ noiseLevel p := by linarith [hs.1, hs.2.1]
  have hl : 0 ≤ confidence p := by linarith [confidence_one_le p hv]
  have hmc := (macroCalls_upper p hv).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (macro_coefficient_upper p hv) hl) (Real.rpow_nonneg hS _))
  have ht := mul_le_mul_of_nonneg_left hmc (show (0 : ℝ) ≤ (macroCount p : ℝ) from Nat.cast_nonneg _)
  have hn := mul_le_mul_of_nonneg_left (macro_noise_upper p hv)
    (show 0 ≤ (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 16) * confidence p by positivity)
  have hid : (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 41) =
      (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 16) * 33554432 := by
    rw [show 24 * tailPower p + 8 / (p.q - 1) + 41 =
      (24 * tailPower p + 8 / (p.q - 1) + 16) + 25 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simp only [trialCalls, tuned_macros, Nat.cast_mul]
  rw [hid]
  ring_nf at ht hn ⊢
  exact ht.trans hn

lemma confidence_log_bound {z Y β : ℝ} (hz : 0 ≤ z) (hY : 1 ≤ Y) (hβ : 2 ≤ β)
    (hbound : z ≤ (2 : ℝ) ^ 56 * Y ^ (2 * β + 4)) :
    1 + Real.log (1 + z) ≤ 64 * (β + 1) * (1 + Real.log Y) := by
  have hYpos : 0 < Y := by linarith
  have hpow : 1 ≤ Y ^ (2 * β + 4) := Real.one_le_rpow hY (by linarith)
  have hsum : 1 + z ≤ (2 : ℝ) ^ 57 * Y ^ (2 * β + 4) := by
    norm_num at hbound ⊢
    linarith
  have hh := Real.log_le_log (show 0 < 1 + z by linarith) hsum
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 57 ≠ 0)
    (ne_of_gt (Real.rpow_pos_of_pos hYpos _)), Real.log_pow, Real.log_rpow hYpos] at hh
  have hlog := Real.log_nonneg hY
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hh htwo
  nlinarith

lemma confidence_argument_bound (p : Params) (hv : spec.valid p) :
    ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2 ≤
      180 * ((macroCount p : ℝ) * (epochCount p : ℝ)) ^ 2 * (guardRadius p / targetAccuracy p) ^ 2 := by
  have hm : 1 ≤ (epochCount p : ℝ) := by exact_mod_cast epochCount_pos p hv
  have hJ : 1 ≤ (macroCount p : ℝ) := by exact_mod_cast macroCount_pos p
  have hK : 1 ≤ (logicalBlocks p : ℝ) := by exact_mod_cast logicalBlocks_pos p
  have hk := logicalBlocks_upper p hv
  have hJm : (macroCount p : ℝ) ≤ (macroCount p : ℝ) * (epochCount p : ℝ) := by nlinarith
  have hsum : ((logicalBlocks p + macroCount p : ℕ) : ℝ) ≤ 6 * (macroCount p : ℝ) * (epochCount p : ℝ) := by
    push_cast
    linarith
  have hmoment : momentBound p ≤ 30 * (macroCount p : ℝ) * (epochCount p : ℝ) * (guardRadius p) ^ 2 := by
    unfold momentBound
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hprod := mul_le_mul hsum hmoment (le_of_lt (momentBound_pos p hv)) (by positivity)
  have hd := div_le_div_of_nonneg_right hprod (sq_nonneg (targetAccuracy p))
  convert hd using 1; ring

lemma confidence_argument_scaled (p : Params) (hv : spec.valid p) :
    ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2 ≤
      (2 : ℝ) ^ 56 * ((noiseLevel p) ^ tailPower p) ^ 2 *
        (1 + p.Δ * localScale p / (targetAccuracy p) ^ 2) ^ 2 * (guardRadius p / targetAccuracy p) ^ 2 := by
  have hH := localScale_nonneg p hv
  have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
  have hs := noise_scales p hv
  have hS : 0 ≤ noiseLevel p := by linarith [hs.1, hs.2.1]
  have hpow := sq_le_sq₀ (show (0 : ℝ) ≤ (macroCount p : ℝ) * (epochCount p : ℝ) by positivity)
    (show 0 ≤ 16777216 * (noiseLevel p) ^ tailPower p * (1 + p.Δ * localScale p / (targetAccuracy p) ^ 2) by positivity)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (hpow.mpr (macro_epoch_upper p hv)) (show (0 : ℝ) ≤ 180 by norm_num))
    (sq_nonneg (guardRadius p / targetAccuracy p))
  apply (confidence_argument_bound p hv).trans
  apply hh.trans
  have hn : 0 ≤ ((noiseLevel p) ^ tailPower p) ^ 2 *
      (1 + p.Δ * localScale p / (targetAccuracy p) ^ 2) ^ 2 * (guardRadius p / targetAccuracy p) ^ 2 := by positivity
  norm_num
  nlinarith only [hn]

lemma confidence_upper (p : Params) (hv : spec.valid p) :
    confidence p ≤ 64 * (tailPower p + 1) *
      (1 + Real.log (2 + noiseLevel p + p.Δ * localScale p / (targetAccuracy p) ^ 2 + guardRadius p / targetAccuracy p)) := by
  let Y := 2 + noiseLevel p + p.Δ * localScale p / (targetAccuracy p) ^ 2 + guardRadius p / targetAccuracy p
  have hH := localScale_nonneg p hv
  have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
  have hs := noise_scales p hv
  have hS : 1 ≤ noiseLevel p := hs.1.trans hs.2.1
  have hD : 0 ≤ p.Δ * localScale p / (targetAccuracy p) ^ 2 := by positivity
  have hR : 0 ≤ guardRadius p / targetAccuracy p :=
    div_nonneg (guardRadius_bounds p hv).1.le (targetAccuracy_pos p hv).le
  have hY : 1 ≤ Y := by dsimp [Y]; linarith
  have hYS : noiseLevel p ≤ Y := by dsimp [Y]; linarith
  have hYD : 1 + p.Δ * localScale p / (targetAccuracy p) ^ 2 ≤ Y := by dsimp [Y]; linarith
  have hYR : guardRadius p / targetAccuracy p ≤ Y := by dsimp [Y]; linarith
  have hb := tailPower_two_le p hv
  have hSp := Real.rpow_le_rpow (by linarith : 0 ≤ noiseLevel p) hYS (show 0 ≤ tailPower p by linarith)
  have hSsq := (sq_le_sq₀ (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith : 0 ≤ Y) _)).mpr hSp
  have hDsq := (sq_le_sq₀ (by linarith : 0 ≤ 1 + p.Δ * localScale p / (targetAccuracy p) ^ 2)
    (by linarith : 0 ≤ Y)).mpr hYD
  have hRsq := (sq_le_sq₀ hR (by linarith : 0 ≤ Y)).mpr hYR
  have hprod := mul_le_mul (mul_le_mul hSsq hDsq (sq_nonneg _) (sq_nonneg _)) hRsq
    (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hid : (Y ^ tailPower p) ^ 2 * Y ^ 2 * Y ^ 2 = Y ^ (2 * tailPower p + 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Y)]
    rw [← Real.rpow_two Y, ← Real.rpow_add (by linarith : 0 < Y), ← Real.rpow_add (by linarith : 0 < Y)]
    congr 1
    ring
  rw [hid] at hprod
  have hbound := (confidence_argument_scaled p hv).trans (show
      (2 : ℝ) ^ 56 * ((noiseLevel p) ^ tailPower p) ^ 2 *
        (1 + p.Δ * localScale p / (targetAccuracy p) ^ 2) ^ 2 * (guardRadius p / targetAccuracy p) ^ 2 ≤
      (2 : ℝ) ^ 56 * Y ^ (2 * tailPower p + 4) by
    convert mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 ^ 56 by positivity) using 1; ring)
  exact confidence_log_bound (by positivity [momentBound_pos p hv]) hY hb hbound

noncomputable def publicNoise (p : Params) : ℝ := 1 + p.σg / p.ε + p.αg

noncomputable def publicRadius (p : Params) : ℝ := p.ε + p.σg / (1 + p.αg)

noncomputable def publicScale (p : Params) : ℝ := p.L0 + p.σh + (p.L1 + p.αh) * publicRadius p

noncomputable def publicGapFactor (p : Params) : ℝ := p.Δ * publicScale p / p.ε ^ 2

noncomputable def publicGuardFactor (p : Params) : ℝ :=
  (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε + p.σg) / p.ε

noncomputable def publicLogArgument (p : Params) : ℝ :=
  2 + publicNoise p + publicGapFactor p + publicGuardFactor p

noncomputable def publicRateCore (p : Params) : ℝ :=
  (publicNoise p) ^ tailPower p + publicGapFactor p *
    ((publicNoise p) ^ (tailPower p / p.q) + (relativeNoise p) ^ 2 * (publicNoise p) ^ (tailPower p - 2))

lemma public_scales (p : Params) (hv : spec.valid p) :
    1 ≤ publicNoise p ∧ 0 ≤ publicGapFactor p ∧ 0 ≤ publicGuardFactor p ∧
    noiseLevel p ≤ 2 * publicNoise p ∧ localRadius p ≤ publicRadius p ∧ localScale p ≤ publicScale p ∧
    p.Δ * localScale p / (targetAccuracy p) ^ 2 ≤ 4 * publicGapFactor p ∧
    guardRadius p / targetAccuracy p ≤ 32 * publicGuardFactor p := by
  have hs := noise_scales p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, he⟩
  have hA : 0 < 1 + p.αg := by linarith
  have hratio : 0 ≤ p.σg / p.ε := div_nonneg hσg he.le
  have hrad : localRadius p ≤ publicRadius p := by
    dsimp [localRadius, publicRadius, targetAccuracy, relativeNoise]
    linarith
  have hH : localScale p ≤ publicScale p := by
    dsimp [localScale, publicScale]
    linarith [mul_le_mul_of_nonneg_left hrad (add_nonneg hL1 hαh)]
  have hH0 : 0 ≤ publicScale p := by dsimp [publicScale, publicRadius]; positivity
  have hsg : p.σg / (1 + p.αg) ≤ p.σg := (div_le_iff₀ hA).mpr (by nlinarith)
  refine ⟨by dsimp [publicNoise]; linarith, by dsimp [publicGapFactor]; positivity,
    by dsimp [publicGuardFactor]; positivity, ?_, hrad, hH, ?_, ?_⟩
  · dsimp [noiseLevel, publicNoise, targetAccuracy]
    have hid : p.σg / (p.ε / 2) = 2 * (p.σg / p.ε) := by ring
    rw [hid]
    linarith
  · have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH hΔ) (sq_nonneg p.ε)
    dsimp [publicGapFactor, targetAccuracy]
    convert mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 4 by norm_num) using 1; ring
  · dsimp [guardRadius, targetAccuracy, publicGuardFactor, localRadius, relativeNoise]
    have hh := div_le_div_of_nonneg_right (show
        16 * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + (p.ε / 2 + p.σg / (1 + p.αg))) ≤
        16 * (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε + p.σg) by linarith) he.le
    convert mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring

lemma publicLogArgument_one_le (p : Params) (hv : spec.valid p) : 1 ≤ publicLogArgument p := by
  have hs := public_scales p hv
  dsimp [publicLogArgument]
  linarith [hs.1, hs.2.1, hs.2.2.1]

lemma confidence_public_upper (p : Params) (hv : spec.valid p) :
    confidence p ≤ 384 * (tailPower p + 1) * (1 + Real.log (publicLogArgument p)) := by
  have hs := public_scales p hv
  have hi := noise_scales p hv
  have hY := publicLogArgument_one_le p hv
  have hM := (guardRadius_bounds p hv).1
  have he := targetAccuracy_pos p hv
  have hH := localScale_nonneg p hv
  have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
  have hargpos : 0 < 2 + noiseLevel p + p.Δ * localScale p / (targetAccuracy p) ^ 2 + guardRadius p / targetAccuracy p := by
    have hS : 0 < noiseLevel p := by linarith [hi.1, hi.2.1]
    positivity
  have harg : 2 + noiseLevel p + p.Δ * localScale p / (targetAccuracy p) ^ 2 + guardRadius p / targetAccuracy p ≤
      32 * publicLogArgument p := by
    dsimp [publicLogArgument]
    linarith [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2]
  have hh := Real.log_le_log hargpos harg
  rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (by linarith : publicLogArgument p ≠ 0)] at hh
  have hlog32 : Real.log 32 ≤ 5 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlog := Real.log_nonneg hY
  have hb := tailPower_two_le p hv
  have hmul := mul_le_mul_of_nonneg_left (show
      1 + Real.log (2 + noiseLevel p + p.Δ * localScale p / (targetAccuracy p) ^ 2 + guardRadius p / targetAccuracy p) ≤
      6 * (1 + Real.log (publicLogArgument p)) by linarith)
    (show 0 ≤ 64 * (tailPower p + 1) by linarith)
  exact (confidence_upper p hv).trans (by convert hmul using 1; ring)

lemma noise_power_scaling (p : Params) (hv : spec.valid p) {t : ℝ} (ht : 0 ≤ t) (htβ : t ≤ tailPower p) :
    (noiseLevel p) ^ t ≤ (2 : ℝ) ^ tailPower p * (publicNoise p) ^ t := by
  have hs := public_scales p hv
  have hi := noise_scales p hv
  have hh := Real.rpow_le_rpow (show 0 ≤ noiseLevel p by linarith [hi.1, hi.2.1]) hs.2.2.2.1 ht
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (show 0 ≤ publicNoise p by linarith [hs.1])] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) htβ)
    (Real.rpow_nonneg (by linarith [hs.1]) _))

lemma publicRateCore_nonneg (p : Params) (hv : spec.valid p) : 0 ≤ publicRateCore p := by
  have hs := public_scales p hv
  have hS : 0 ≤ publicNoise p := by linarith [hs.1]
  have hD := hs.2.1
  dsimp [publicRateCore]
  positivity

lemma rate_core_scaling (p : Params) (hv : spec.valid p) :
    (noiseLevel p) ^ tailPower p + p.Δ * localScale p / (targetAccuracy p) ^ 2 *
      ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2)) ≤
      (2 : ℝ) ^ (tailPower p + 2) * publicRateCore p := by
  have hs := public_scales p hv
  have hi := noise_scales p hv
  have hS : 0 ≤ noiseLevel p := by linarith [hi.1, hi.2.1]
  have hS0 : 0 ≤ publicNoise p := by linarith [hs.1]
  have hb := tailPower_two_le p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hquot : tailPower p / p.q ≤ tailPower p := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have hB := noise_power_scaling p hv (t := tailPower p) (by linarith) le_rfl
  have hV := noise_power_scaling p hv (t := tailPower p / p.q) (by positivity) hquot
  have hT := mul_le_mul_of_nonneg_left (noise_power_scaling p hv (t := tailPower p - 2) (by linarith) (by linarith))
    (sq_nonneg (relativeNoise p))
  have hsum := add_le_add hV hT
  have hprod := mul_le_mul hs.2.2.2.2.2.2.1 hsum (by positivity)
    (show 0 ≤ 4 * publicGapFactor p by linarith [hs.2.1])
  have hB0 : 0 ≤ (2 : ℝ) ^ tailPower p * (publicNoise p) ^ tailPower p := by positivity
  have hid : (2 : ℝ) ^ (tailPower p + 2) = 4 * (2 : ℝ) ^ tailPower p := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  rw [hid]
  dsimp [publicRateCore]
  ring_nf at hB hprod hB0 ⊢
  linarith only [hB, hprod, hB0]

lemma public_constant_bound (p : Params) (hv : spec.valid p) :
    (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 41) * 384 * (2 : ℝ) ^ (tailPower p + 2) ≤
      (2 : ℝ) ^ (32 * tailPower p + 16 * p.q / (p.q - 1) + 64) := by
  have hb := tailPower_two_le p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hquot : 8 / (p.q - 1) ≤ 16 * p.q / (p.q - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (384 : ℝ) ≤ 2 ^ (9 : ℝ) by norm_num)
    (show 0 ≤ (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 41) by positivity))
    (show 0 ≤ (2 : ℝ) ^ (tailPower p + 2) by positivity)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hh
  exact hh.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

lemma trialCalls_public_upper (p : Params) (hv : spec.valid p) :
    (trialCalls (tunedConfig p) : ℝ) ≤
      (2 : ℝ) ^ (32 * tailPower p + 16 * p.q / (p.q - 1) + 64) * (tailPower p + 1) *
        (1 + Real.log (publicLogArgument p)) * publicRateCore p := by
  have hb := tailPower_two_le p hv
  have hlog := Real.log_nonneg (publicLogArgument_one_le p hv)
  have hcore := publicRateCore_nonneg p hv
  have hconf := confidence_public_upper p hv
  have hrate := rate_core_scaling p hv
  have htrial := trialCalls_upper p hv
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hconf
    (show 0 ≤ (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 41) by positivity)) hrate
    (show 0 ≤ (noiseLevel p) ^ tailPower p + p.Δ * localScale p / (targetAccuracy p) ^ 2 *
      ((noiseLevel p) ^ (tailPower p / p.q) + (relativeNoise p) ^ 2 * (noiseLevel p) ^ (tailPower p - 2)) by
      have hs := noise_scales p hv
      have hS : 0 ≤ noiseLevel p := by linarith [hs.1, hs.2.1]
      have hH := localScale_nonneg p hv
      have hΔ : 0 ≤ p.Δ := hv.2.2.2.2.2.2.2.2.2.2.1
      positivity)
    (show 0 ≤ (2 : ℝ) ^ (24 * tailPower p + 8 / (p.q - 1) + 41) *
      (384 * (tailPower p + 1) * (1 + Real.log (publicLogArgument p))) by positivity)
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (public_constant_bound p hv) (show 0 ≤ tailPower p + 1 by linarith))
    (show 0 ≤ 1 + Real.log (publicLogArgument p) by linarith)) hcore
  apply htrial.trans (hh.trans _)
  convert hc using 1; ring

noncomputable def envelope (p : Params) : ℝ :=
  (2 : ℝ) ^ (32 * tailPower p + 16 * p.q / (p.q - 1) + 64) * (tailPower p + 1) *
    (1 + Real.log (publicLogArgument p)) * publicRateCore p

lemma calls_le_budget (p : Params) (hv : spec.valid p) :
    trialCalls (tunedConfig p) ≤ ⌈envelope p⌉₊ := by
  exact_mod_cast (trialCalls_public_upper p hv).trans (Nat.le_ceil (envelope p))

end LongTails.Proofs.HystereticHessianBudget
