import LongTails.Proofs.AffineMomentParameters

open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentParameters

namespace LongTails.Proofs.AffineMomentBudget

lemma iterations_bound {t : Tuning} (ht : Valid t) {V l : ℝ}
    (hV : 1 ≤ V) (he : 1 / t.ε ≤ V) (hl : confidence t ≤ l) :
    (iterations t : ℝ) ≤ 2 ^ 49 * l * V ^ (t.p / (3 * t.p - 2)) := by
  let r := t.p / (3 * t.p - 2)
  have hr : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by linarith [ht.exponent_gt]) (by linarith [ht.exponent_gt])
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one (by linarith [ht.exponent_gt])).mpr
    linarith [ht.exponent_gt]
  have hc := confidence_ge_one ht
  have hl1 : 1 ≤ l := hc.trans hl
  have he0 := one_div_pos.mpr ht.accuracy_pos
  have hX : 1 ≤ (2 : ℝ) ^ 48 * confidence t / t.ε := by
    apply (le_div_iff₀ ht.accuracy_pos).mpr
    nlinarith [ht.accuracy_le]
  have hpow1 : 1 ≤ ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r :=
    Real.one_le_rpow hX hr
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r by positivity)
  change (iterations t : ℝ) < ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r + 1 at hceil
  have hb : ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r ≤
      (2 : ℝ) ^ 48 * l * V ^ r := by
    calc
      _ ≤ ((2 : ℝ) ^ 48 * l * V) ^ r := by
        apply Real.rpow_le_rpow (by positivity) _ hr
        rw [div_eq_mul_inv]
        have hh := mul_le_mul hl he he0.le (by linarith : 0 ≤ l)
        simpa only [one_div, mul_assoc] using mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 ^ 48)
      _ = ((2 : ℝ) ^ 48 * l) ^ r * V ^ r := Real.mul_rpow (by positivity) (by linarith)
      _ ≤ ((2 : ℝ) ^ 48 * l) * V ^ r := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by nlinarith : (1 : ℝ) ≤ 2 ^ 48 * l) hr1
  dsimp [r] at hpow1 hceil hb
  nlinarith

lemma iterations_sharp_bound {t : Tuning} (ht : Valid t) {V l : ℝ}
    (hV : 1 ≤ V) (he : 1 / t.ε ≤ V) (hl : confidence t ≤ l) :
    (iterations t : ℝ) ≤ 2 ^ 49 * l ^ (t.p / (3 * t.p - 2)) * V ^ (t.p / (3 * t.p - 2)) := by
  let r := t.p / (3 * t.p - 2)
  have hr : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by linarith [ht.exponent_gt]) (by linarith [ht.exponent_gt])
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one (by linarith [ht.exponent_gt])).mpr
    linarith [ht.exponent_gt]
  have hc := confidence_ge_one ht
  have hl1 : 1 ≤ l := hc.trans hl
  have he0 := one_div_pos.mpr ht.accuracy_pos
  have hX : 1 ≤ (2 : ℝ) ^ 48 * confidence t / t.ε := by
    apply (le_div_iff₀ ht.accuracy_pos).mpr
    nlinarith [ht.accuracy_le]
  have hpow1 : 1 ≤ ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r :=
    Real.one_le_rpow hX hr
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r by positivity)
  change (iterations t : ℝ) < ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r + 1 at hceil
  have hb : ((2 : ℝ) ^ 48 * confidence t / t.ε) ^ r ≤
      (2 : ℝ) ^ 48 * l ^ r * V ^ r := by
    calc
      _ ≤ ((2 : ℝ) ^ 48 * l * V) ^ r := by
        apply Real.rpow_le_rpow (by positivity) _ hr
        rw [div_eq_mul_inv]
        have hh := mul_le_mul hl he he0.le (by linarith : 0 ≤ l)
        simpa only [one_div, mul_assoc] using mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 ^ 48)
      _ = ((2 : ℝ) ^ 48 * l) ^ r * V ^ r := Real.mul_rpow (by positivity) (by linarith)
      _ = ((2 : ℝ) ^ 48) ^ r * l ^ r * V ^ r := by
        rw [Real.mul_rpow (by positivity) (by linarith : 0 ≤ l)]
      _ ≤ (2 : ℝ) ^ 48 * l ^ r * V ^ r := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2 ^ 48) hr1
  dsimp [r] at hpow1 hceil hb
  nlinarith

lemma groups_bound {t : Tuning} (ht : Valid t) {l : ℝ} (hl : confidence t ≤ l) :
    (pilotGroups t : ℝ) ≤ 2048 * conjugate t * l := by
  have hq := conjugate_ge_two ht
  have hc := confidence_ge_one ht
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 1024 * conjugate t * confidence t by positivity)
  change (pilotGroups t : ℝ) < 1024 * conjugate t * confidence t + 1 at hh
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1024 * conjugate t by positivity)
  nlinarith

lemma add_power_bound {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
  rcases le_total a b with hab | hba
  · have h := Real.rpow_le_rpow (by positivity : 0 ≤ a + b)
      (show a + b ≤ 2 * b by linarith) hq
    rw [Real.mul_rpow (by norm_num) hb] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg ha q)) (by positivity))
  · have h := Real.rpow_le_rpow (by positivity : 0 ≤ a + b)
      (show a + b ≤ 2 * a by linarith) hq
    rw [Real.mul_rpow (by norm_num) ha] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hb q)) (by positivity))

lemma batch_bound {t : Tuning} (ht : Valid t) :
    (batchSize t : ℝ) ≤ 2 * (65536 * (1 + noiseScale t)) ^ conjugate t := by
  have hq := conjugate_ge_two ht
  have hs := noiseScale_nonneg ht
  have hx : 1 ≤ 65536 * (1 + noiseScale t) := by linarith
  have hp := Real.one_le_rpow hx (show 0 ≤ conjugate t by linarith)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ (65536 * (1 + noiseScale t)) ^ conjugate t by positivity)
  change (batchSize t : ℝ) < (65536 * (1 + noiseScale t)) ^ conjugate t + 1 at hh
  linarith

lemma pilot_power_identity {t : Tuning} (ht : Valid t) :
    (pilotRadius t)⁻¹ ^ conjugate t = (iterations t : ℝ) ^ (conjugate t + 1) := by
  have hK : 0 < (iterations t : ℝ) := by exact_mod_cast iterations_pos ht
  have hp := ht.exponent_gt
  unfold pilotRadius conjugate
  rw [← Real.rpow_neg_one, ← Real.rpow_mul hK.le, ← Real.rpow_mul hK.le]
  congr 1
  field_simp [show t.p ≠ 0 by linarith, show t.p - 1 ≠ 0 by linarith]
  ring

lemma weighted_noise {t : Tuning} (ht : Valid t) :
    (iterations t : ℝ) * (1 + noiseScale t) ^ conjugate t ≤
      (2 : ℝ) ^ conjugate t * ((1 + t.σ) ^ conjugate t * (iterations t : ℝ) +
        t.σ0 ^ conjugate t * (iterations t : ℝ) ^ (conjugate t + 2)) := by
  have hK : 0 < (iterations t : ℝ) := by exact_mod_cast iterations_pos ht
  have hν := pilotRadius_pos ht
  have hq := conjugate_ge_two ht
  have hs := ht.noise_nonneg
  have h0 := ht.additive_nonneg
  have hsplit := add_power_bound (show 0 ≤ 1 + t.σ by linarith)
    (show 0 ≤ t.σ0 / pilotRadius t by positivity) (show 0 ≤ conjugate t by linarith)
  have hid : (iterations t : ℝ) * (t.σ0 / pilotRadius t) ^ conjugate t =
      t.σ0 ^ conjugate t * (iterations t : ℝ) ^ (conjugate t + 2) := by
    rw [div_eq_mul_inv, Real.mul_rpow h0 (inv_nonneg.mpr hν.le), pilot_power_identity ht]
    have hpow : (iterations t : ℝ) ^ (conjugate t + 2) =
        (iterations t : ℝ) * (iterations t : ℝ) ^ (conjugate t + 1) := by
      conv_lhs => rw [show conjugate t + 2 = 1 + (conjugate t + 1) by ring,
        Real.rpow_add hK, Real.rpow_one]
    rw [hpow]
    ring
  have hh := mul_le_mul_of_nonneg_left hsplit hK.le
  change (iterations t : ℝ) * (1 + (t.σ + t.σ0 / pilotRadius t)) ^ conjugate t ≤ _
  rw [← add_assoc]
  calc
    _ ≤ (iterations t : ℝ) * ((2 : ℝ) ^ conjugate t *
        ((1 + t.σ) ^ conjugate t + (t.σ0 / pilotRadius t) ^ conjugate t)) := hh
    _ = (2 : ℝ) ^ conjugate t * ((1 + t.σ) ^ conjugate t * (iterations t : ℝ) +
        (iterations t : ℝ) * (t.σ0 / pilotRadius t) ^ conjugate t) := by ring
    _ = _ := by rw [hid]

lemma calls_intermediate {t : Tuning} (ht : Valid t) {l : ℝ}
    (hl : confidence t ≤ l) :
    (iterations t * blockSize t : ℝ) ≤
      8192 * conjugate t * (131072 : ℝ) ^ conjugate t * l *
        ((1 + t.σ) ^ conjugate t * (iterations t : ℝ) +
          t.σ0 ^ conjugate t * (iterations t : ℝ) ^ (conjugate t + 2)) := by
  have hG := groups_bound ht hl
  have hB := batch_bound ht
  have hs := noiseScale_nonneg ht
  have hl0 : 0 ≤ l := by linarith [confidence_ge_one ht]
  have hq := conjugate_ge_two ht
  have hw := weighted_noise ht
  have hpow : (65536 * (1 + noiseScale t)) ^ conjugate t =
      (65536 : ℝ) ^ conjugate t * (1 + noiseScale t) ^ conjugate t :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hc : (65536 : ℝ) ^ conjugate t * (2 : ℝ) ^ conjugate t =
      (131072 : ℝ) ^ conjugate t := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  calc
    _ = (iterations t : ℝ) * (2 * ((batchSize t : ℝ) * pilotGroups t)) := by
      simp only [blockSize, sampleSize, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ (iterations t : ℝ) * (2 * ((2 * (65536 * (1 + noiseScale t)) ^ conjugate t) *
        (2048 * conjugate t * l))) := by gcongr
    _ = (8192 * conjugate t * (65536 : ℝ) ^ conjugate t * l) *
        ((iterations t : ℝ) * (1 + noiseScale t) ^ conjugate t) := by rw [hpow]; ring
    _ ≤ (8192 * conjugate t * (65536 : ℝ) ^ conjugate t * l) *
        ((2 : ℝ) ^ conjugate t * ((1 + t.σ) ^ conjugate t * (iterations t : ℝ) +
          t.σ0 ^ conjugate t * (iterations t : ℝ) ^ (conjugate t + 2))) := by gcongr
    _ = 8192 * conjugate t * ((65536 : ℝ) ^ conjugate t * (2 : ℝ) ^ conjugate t) * l *
        ((1 + t.σ) ^ conjugate t * (iterations t : ℝ) +
          t.σ0 ^ conjugate t * (iterations t : ℝ) ^ (conjugate t + 2)) := by ring
    _ = _ := by rw [hc]

lemma rate_conjugate {t : Tuning} (ht : Valid t) :
    t.p / (3 * t.p - 2) * (conjugate t + 2) = conjugate t := by
  have hp := ht.exponent_gt
  unfold conjugate
  apply (eq_div_iff (show t.p - 1 ≠ 0 by linarith)).mpr
  rw [mul_assoc, add_mul, div_mul_cancel₀ _ (show t.p - 1 ≠ 0 by linarith),
    show t.p + 2 * (t.p - 1) = 3 * t.p - 2 by ring,
    div_mul_cancel₀ _ (show 3 * t.p - 2 ≠ 0 by linarith)]

lemma iterations_products {t : Tuning} (ht : Valid t) {V l : ℝ}
    (hV : 1 ≤ V) (he : 1 / t.ε ≤ V) (hl : confidence t ≤ l) :
    l * (iterations t : ℝ) ≤
      (2 : ℝ) ^ 49 * l ^ (conjugate t + 1) * V ^ (t.p / (3 * t.p - 2)) ∧
    l * (iterations t : ℝ) ^ (conjugate t + 2) ≤
      ((2 : ℝ) ^ 49) ^ (conjugate t + 2) * l ^ (conjugate t + 1) * V ^ conjugate t := by
  have hl1 : 1 ≤ l := (confidence_ge_one ht).trans hl
  have hl0 : 0 < l := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hp := ht.exponent_gt
  have hq := conjugate_ge_two ht
  have hr : 0 ≤ t.p / (3 * t.p - 2) := div_nonneg (by linarith) (by linarith)
  have hr1 : t.p / (3 * t.p - 2) ≤ 1 := by
    apply (div_le_one (by linarith)).mpr
    linarith
  have hK := iterations_sharp_bound ht hV he hl
  have hpow : (l ^ (t.p / (3 * t.p - 2))) ^ (conjugate t + 2) = l ^ conjugate t := by
    rw [← Real.rpow_mul hl0.le, rate_conjugate ht]
  have hpowV : (V ^ (t.p / (3 * t.p - 2))) ^ (conjugate t + 2) = V ^ conjugate t := by
    rw [← Real.rpow_mul hV0, rate_conjugate ht]
  have hcombine : l * l ^ conjugate t = l ^ (conjugate t + 1) := by
    rw [Real.rpow_add hl0, Real.rpow_one]
    ring
  constructor
  · have hsmall : l ^ (t.p / (3 * t.p - 2)) ≤ l ^ conjugate t :=
      Real.rpow_le_rpow_of_exponent_le hl1 (by linarith)
    calc
      _ ≤ l * ((2 : ℝ) ^ 49 * l ^ (t.p / (3 * t.p - 2)) * V ^ (t.p / (3 * t.p - 2))) := by gcongr
      _ ≤ l * ((2 : ℝ) ^ 49 * l ^ conjugate t * V ^ (t.p / (3 * t.p - 2))) := by gcongr
      _ = _ := by rw [← hcombine]; ring
  · have h := Real.rpow_le_rpow (by positivity : 0 ≤ (iterations t : ℝ)) hK
      (show 0 ≤ conjugate t + 2 by linarith)
    have hfactor : ((2 : ℝ) ^ 49 * l ^ (t.p / (3 * t.p - 2)) *
        V ^ (t.p / (3 * t.p - 2))) ^ (conjugate t + 2) =
        ((2 : ℝ) ^ 49) ^ (conjugate t + 2) * l ^ conjugate t * V ^ conjugate t := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity), hpow, hpowV]
    rw [hfactor] at h
    calc
      _ ≤ l * (((2 : ℝ) ^ 49) ^ (conjugate t + 2) * l ^ conjugate t * V ^ conjugate t) := by gcongr
      _ = _ := by rw [← hcombine]; ring

lemma coefficient_bound {q : ℝ} (hq : 2 ≤ q) :
    8192 * q * (131072 : ℝ) ^ q * ((2 : ℝ) ^ 49) ^ (q + 2) ≤ (2 : ℝ) ^ (256 * q) := by
  have hq0 : 0 ≤ q := by linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hqexp : q ≤ (2 : ℝ) ^ (2 * q) := by
    calc
      q ≤ Real.exp q := (Real.add_one_le_exp q).trans' (by linarith)
      _ ≤ Real.exp (Real.log 2 * (2 * q)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (2 * q)).symm
  have he : (8192 : ℝ) * (131072 : ℝ) ^ q * ((2 : ℝ) ^ 49) ^ (q + 2) =
      (2 : ℝ) ^ (66 * q + 111) := by
    rw [show (8192 : ℝ) = (2 : ℝ) ^ (13 : ℝ) by norm_num,
      show (131072 : ℝ) = (2 : ℝ) ^ (17 : ℝ) by norm_num,
      show (2 : ℝ) ^ (49 : ℕ) = (2 : ℝ) ^ (49 : ℝ) by norm_cast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc
    _ = q * ((8192 : ℝ) * (131072 : ℝ) ^ q * ((2 : ℝ) ^ 49) ^ (q + 2)) := by ring
    _ = q * (2 : ℝ) ^ (66 * q + 111) := by rw [he]
    _ ≤ (2 : ℝ) ^ (2 * q) * (2 : ℝ) ^ (66 * q + 111) := by gcongr
    _ = (2 : ℝ) ^ (68 * q + 111) := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma calls_bound {t : Tuning} (ht : Valid t) {V l : ℝ}
    (hV : 1 ≤ V) (he : 1 / t.ε ≤ V) (hl : confidence t ≤ l) :
    (iterations t * blockSize t : ℝ) ≤ (2 : ℝ) ^ (256 * conjugate t) *
      ((1 + t.σ) ^ conjugate t * V ^ (t.p / (3 * t.p - 2)) +
        (t.σ0 * V) ^ conjugate t) * l ^ (conjugate t + 1) := by
  have hl0 : 0 ≤ l := by linarith [confidence_ge_one ht]
  have hV0 : 0 ≤ V := by linarith
  have hq := conjugate_ge_two ht
  have hs := ht.noise_nonneg
  have h0 := ht.additive_nonneg
  have hc := coefficient_bound hq
  have hproducts := iterations_products ht hV he hl
  have hd : (2 : ℝ) ^ 49 ≤ ((2 : ℝ) ^ 49) ^ (conjugate t + 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2 ^ 49) (show (1 : ℝ) ≤ conjugate t + 2 by linarith)
  have hfirst : l * (iterations t : ℝ) ≤
      ((2 : ℝ) ^ 49) ^ (conjugate t + 2) * l ^ (conjugate t + 1) * V ^ (t.p / (3 * t.p - 2)) := by
    exact hproducts.1.trans (by gcongr)
  calc
    _ ≤ 8192 * conjugate t * (131072 : ℝ) ^ conjugate t * l *
        ((1 + t.σ) ^ conjugate t * (iterations t : ℝ) +
          t.σ0 ^ conjugate t * (iterations t : ℝ) ^ (conjugate t + 2)) := calls_intermediate ht hl
    _ = (8192 * conjugate t * (131072 : ℝ) ^ conjugate t) *
        ((1 + t.σ) ^ conjugate t * (l * (iterations t : ℝ)) +
          t.σ0 ^ conjugate t * (l * (iterations t : ℝ) ^ (conjugate t + 2))) := by ring
    _ ≤ (8192 * conjugate t * (131072 : ℝ) ^ conjugate t) *
        ((1 + t.σ) ^ conjugate t * (((2 : ℝ) ^ 49) ^ (conjugate t + 2) *
          l ^ (conjugate t + 1) * V ^ (t.p / (3 * t.p - 2))) +
          t.σ0 ^ conjugate t * (((2 : ℝ) ^ 49) ^ (conjugate t + 2) *
          l ^ (conjugate t + 1) * V ^ conjugate t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity))
        (mul_le_mul_of_nonneg_left hproducts.2 (by positivity))
    _ = (8192 * conjugate t * (131072 : ℝ) ^ conjugate t * ((2 : ℝ) ^ 49) ^ (conjugate t + 2)) *
        ((1 + t.σ) ^ conjugate t * V ^ (t.p / (3 * t.p - 2)) +
          (t.σ0 * V) ^ conjugate t) * l ^ (conjugate t + 1) := by
      rw [Real.mul_rpow h0 hV0]
      ring
    _ ≤ _ := by gcongr

lemma setup_inverse (p : LongTails.Setups.AffineMomentConvex.Params)
    (hp : LongTails.Setups.AffineMomentConvex.spec.valid p) :
    1 / (tuning p).ε ≤ 4 + p.L * p.R ^ 2 / p.ε := by
  rcases hp with ⟨hL, hR, hσ, hσ0, hα, hα2, hε, hδ, hδ1⟩
  have hden : 0 < p.L * p.R ^ 2 := by positivity
  dsimp only [tuning]
  by_cases h : p.ε / (p.L * p.R ^ 2) ≤ 1 / 4
  · rw [min_eq_left h, one_div_div]
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    norm_num
    positivity

lemma setup_confidence (p : LongTails.Setups.AffineMomentConvex.Params)
    (hp : LongTails.Setups.AffineMomentConvex.spec.valid p) :
    confidence (tuning p) ≤ Real.log (20 + p.α / (p.α - 1) + p.L * p.R ^ 2 / p.ε + 1 / p.δ) := by
  have ht := tuning_valid p hp
  have hi := setup_inverse p hp
  have hq := conjugate_ge_two ht
  have he := one_div_pos.mpr ht.accuracy_pos
  have hd := one_div_pos.mpr ht.confidence_pos
  unfold confidence
  apply Real.log_le_log (by positivity)
  change 16 + conjugate (tuning p) + 1 / (tuning p).ε + 1 / (tuning p).δ ≤ _
  dsimp only [conjugate, tuning] at *
  linarith


lemma public_calls (p : LongTails.Setups.AffineMomentConvex.Params)
    (hp : LongTails.Setups.AffineMomentConvex.spec.valid p) :
    iterations (tuning p) * blockSize (tuning p) ≤
      ⌈(2 : ℝ) ^ (256 * (p.α / (p.α - 1))) *
        ((1 + p.σ) ^ (p.α / (p.α - 1)) * (4 + p.L * p.R ^ 2 / p.ε) ^ (p.α / (3 * p.α - 2)) +
          (p.σ0 * (4 / (p.L * p.R) + p.R / p.ε)) ^ (p.α / (p.α - 1))) *
        (Real.log (20 + p.α / (p.α - 1) + p.L * p.R ^ 2 / p.ε + 1 / p.δ)) ^ (p.α / (p.α - 1) + 1)⌉₊ := by
  have ht := tuning_valid p hp
  have hL := hp.1
  have hR := hp.2.1
  have hε := hp.2.2.2.2.2.2.1
  have hT : 0 ≤ p.L * p.R ^ 2 / p.ε := by positivity
  have hb := calls_bound ht (show 1 ≤ 4 + p.L * p.R ^ 2 / p.ε by linarith)
    (setup_inverse p hp) (setup_confidence p hp)
  have hfloor : p.σ0 / (p.L * p.R) * (4 + p.L * p.R ^ 2 / p.ε) =
      p.σ0 * (4 / (p.L * p.R) + p.R / p.ε) := by
    field_simp
  dsimp only [tuning, conjugate] at hb
  rw [hfloor] at hb
  apply (Nat.cast_le (α := ℝ)).mp
  push_cast
  exact hb.trans (Nat.le_ceil _)

end LongTails.Proofs.AffineMomentBudget
