import LongTails.Algorithms.AffineMomentAccelerated
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open LongTails.Algorithms.AffineMomentAccelerated

namespace LongTails.Proofs.AffineMomentParameters

lemma weighted_power_balance {p B Q b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hb : 0 ≤ b) :
    B ^ (p / 2) * Q ^ p * b ^ (1 - p / 2) ≤
      (p / 2) * (B * Q ^ 2) + (1 - p / 2) * b := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ p / 2 by linarith) (show 0 ≤ 1 - p / 2 by linarith)
    (show 0 ≤ B * Q ^ 2 by positivity) hb (by ring)
  have he : (B * Q ^ 2) ^ (p / 2) = B ^ (p / 2) * Q ^ p := by
    rw [Real.mul_rpow hB (sq_nonneg Q), ← Real.rpow_two, ← Real.rpow_mul hQ]
    congr 2
    ring
  rwa [he] at h

lemma moment_absorption {p B Q b a c : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha : a ^ p ≤ c * B ^ (p / 2) * b ^ (1 - p / 2)) :
    a ^ p * Q ^ p ≤ c * ((p / 2) * (B * Q ^ 2) + (1 - p / 2) * b) := by
  have h := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hQ p)
  have hw := mul_le_mul_of_nonneg_left (weighted_power_balance hp hp2 hB hQ hb) hc
  nlinarith only [h, hw]

lemma power_weight_of_square {p a B b c : ℝ} (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hb : 0 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hs : a ^ 2 ≤ c ^ 2 * B * b ^ ((2 - p) / p)) :
    a ^ p ≤ c * B ^ (p / 2) * b ^ (1 - p / 2) := by
  have hp0 : 0 < p := by linarith
  have h := Real.rpow_le_rpow (sq_nonneg a) hs (show 0 ≤ p / 2 by positivity)
  have he : (a ^ 2 : ℝ) ^ (p / 2) = a ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_mul ha]
    congr 1
    ring
  have hec : (c ^ 2 : ℝ) ^ (p / 2) = c ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc]
    congr 1
    ring
  have heb : (b ^ ((2 - p) / p)) ^ (p / 2) = b ^ (1 - p / 2) := by
    rw [← Real.rpow_mul hb]
    congr 1
    field_simp
  rw [he, Real.mul_rpow (mul_nonneg (sq_nonneg c) hB) (Real.rpow_nonneg hb _),
    Real.mul_rpow (sq_nonneg c) hB, hec, heb] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_le_one hc hc1 hp)
      (Real.rpow_nonneg hB _)) (Real.rpow_nonneg hb _))

lemma energy_absorption_of_square {p a B Q b : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hb : 0 ≤ b)
    (hs : a ^ 2 ≤ (1 / 65536 : ℝ) ^ 2 * B * b ^ ((2 - p) / p)) :
    20 * a ^ p * Q ^ p ≤ B * Q ^ 2 / 1024 + b := by
  have hw := power_weight_of_square hp ha hB hb (by norm_num : (0 : ℝ) ≤ 1 / 65536)
    (by norm_num) hs
  have hm := moment_absorption (by linarith : 0 ≤ p) hp2 hB hQ hb
    (by norm_num : (0 : ℝ) ≤ 1 / 65536) hw
  have hBQ : 0 ≤ B * Q ^ 2 := mul_nonneg hB (sq_nonneg Q)
  have hpb : 0 ≤ (p / 2) * b := mul_nonneg (by linarith) hb
  have hpB : (p / 2) * (B * Q ^ 2) ≤ B * Q ^ 2 :=
    mul_le_of_le_one_left hBQ (by linarith)
  nlinarith

structure Valid (t : Tuning) : Prop where
  exponent_gt : 1 < t.p
  exponent_le : t.p ≤ 2
  accuracy_pos : 0 < t.ε
  accuracy_le : t.ε ≤ 1 / 4
  confidence_pos : 0 < t.δ
  confidence_lt : t.δ < 1
  noise_nonneg : 0 ≤ t.σ
  additive_nonneg : 0 ≤ t.σ0

lemma tuning_valid (p : LongTails.Setups.AffineMomentConvex.Params)
    (hp : LongTails.Setups.AffineMomentConvex.spec.valid p) : Valid (tuning p) := by
  rcases hp with ⟨hL, hR, hσ, hσ0, hα, hα2, hε, hδ, hδ1⟩
  exact ⟨hα, hα2, lt_min (by positivity) (by norm_num), min_le_right _ _, hδ, hδ1, hσ, by dsimp [tuning]; positivity⟩

lemma conjugate_ge_two {t : Tuning} (ht : Valid t) : 2 ≤ conjugate t := by
  unfold conjugate
  apply (le_div_iff₀ (by linarith [ht.exponent_gt] : 0 < t.p - 1)).mpr
  linarith [ht.exponent_le]

lemma confidence_ge_one {t : Tuning} (ht : Valid t) : 1 ≤ confidence t := by
  have hq := conjugate_ge_two ht
  have he : 0 < 1 / t.ε := one_div_pos.mpr ht.accuracy_pos
  have hd : 0 < 1 / t.δ := one_div_pos.mpr ht.confidence_pos
  unfold confidence
  apply (Real.le_log_iff_exp_le (by linarith)).mpr
  linarith [Real.exp_one_lt_three]

lemma iterations_pos {t : Tuning} (ht : Valid t) : 0 < iterations t := by
  have hl : 0 < confidence t := lt_of_lt_of_le (by norm_num) (confidence_ge_one ht)
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (div_pos (mul_pos (by positivity) hl) ht.accuracy_pos) _

lemma weightScale_pos {t : Tuning} (ht : Valid t) : 0 < weightScale t := by
  have hK : 0 < (iterations t : ℝ) := Nat.cast_pos.mpr (iterations_pos ht)
  unfold weightScale
  positivity

lemma weight_pos {t : Tuning} (ht : Valid t) (k : ℕ) : 0 < weight t k := by
  unfold weight
  exact div_pos (by positivity) (weightScale_pos ht)

lemma accumulatedWeight_nonneg {t : Tuning} (ht : Valid t) (k : ℕ) :
    0 ≤ accumulatedWeight t k := by
  unfold accumulatedWeight
  exact div_nonneg (by positivity) (by have := weightScale_pos ht; positivity)

lemma accumulatedWeight_succ (t : Tuning) (k : ℕ) :
    accumulatedWeight t (k + 1) = accumulatedWeight t k + weight t k := by
  unfold accumulatedWeight weight
  push_cast
  ring

lemma weight_square {t : Tuning} (ht : Valid t) (k : ℕ) :
    weight t k ^ 2 ≤ 2 * accumulatedWeight t (k + 1) / weightScale t := by
  have hD := weightScale_pos ht
  unfold weight accumulatedWeight
  push_cast
  apply (le_div_iff₀ hD).mpr
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma weight_square_scaled {t : Tuning} (ht : Valid t) (k : ℕ) :
    weight t k ^ 2 ≤ (1 / 65536 : ℝ) ^ 2 * accumulatedWeight t (k + 1) *
      (1 / (2 * (iterations t : ℝ))) ^ ((2 - t.p) / t.p) := by
  have hK : 0 < (iterations t : ℝ) := Nat.cast_pos.mpr (iterations_pos ht)
  have hB := accumulatedWeight_nonneg ht (k + 1)
  have hr : 0 < (iterations t : ℝ) ^ ((2 - t.p) / t.p) := Real.rpow_pos_of_pos hK _
  refine (weight_square ht k).trans ?_
  unfold weightScale
  simp only [one_div, Real.inv_rpow (by positivity : 0 ≤ 2 * (iterations t : ℝ))]
  rw [Real.mul_rpow (by norm_num) hK.le]
  have hpow : (2 : ℝ) ^ ((2 - t.p) / t.p) ≤ 2 := by
    have hp := ht.exponent_gt
    have hp2 := ht.exponent_le
    have hexp : (2 - t.p) / t.p ≤ 1 := by
      apply (div_le_one (by linarith : 0 < t.p)).mpr
      linarith
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hpowB := mul_le_mul_of_nonneg_right hpow hB
  have hp2pos : 0 < (2 : ℝ) ^ ((2 - t.p) / t.p) := by positivity
  apply (div_le_iff₀ (mul_pos (by positivity) hr)).mpr
  field_simp
  nlinarith only [hpowB, hB]

lemma weight_energy_absorption {t : Tuning} (ht : Valid t) (k : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) :
    20 * (weight t k) ^ t.p * Q ^ t.p ≤
      accumulatedWeight t (k + 1) * Q ^ 2 / 1024 + 1 / (2 * (iterations t : ℝ)) := by
  exact energy_absorption_of_square (le_of_lt ht.exponent_gt) ht.exponent_le
    (weight_pos ht k).le (accumulatedWeight_nonneg ht _) hQ (by positivity)
    (weight_square_scaled ht k)

lemma pilotRadius_pos {t : Tuning} (ht : Valid t) : 0 < pilotRadius t := by
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (iterations_pos ht)) _

lemma pilotRadius_le_one {t : Tuning} (ht : Valid t) : pilotRadius t ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast iterations_pos ht
  · have hp := ht.exponent_gt
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith

lemma additive_products {p K C : ℝ} (hp : 0 < p) (hK : 0 < K) (hC : 0 < C) :
    (K / (C * K ^ ((2 - p) / p))) ^ p * (K ^ (-(2 * p - 1) / p)) ^ p =
      1 / (C ^ p * K) ∧
    K ^ 2 / (C * K ^ ((2 - p) / p)) * (K ^ (-(2 * p - 1) / p)) ^ 2 =
      1 / (C * K) := by
  have he1 : p + (-(2 * p - 1) / p) * p - ((2 - p) / p) * p = -1 := by
    field_simp
    ring
  have he2 : 2 + (-(2 * p - 1) / p) * 2 - (2 - p) / p = -1 := by
    field_simp
    ring
  constructor
  · rw [Real.div_rpow hK.le (by positivity), Real.mul_rpow hC.le (by positivity),
      ← Real.rpow_mul hK.le, ← Real.rpow_mul hK.le]
    calc
      _ = (K ^ p * K ^ (-(2 * p - 1) / p * p) / K ^ ((2 - p) / p * p)) / C ^ p := by ring
      _ = K ^ (p + (-(2 * p - 1) / p) * p - ((2 - p) / p) * p) / C ^ p := by
        rw [Real.rpow_sub hK, Real.rpow_add hK]
      _ = 1 / (C ^ p * K) := by rw [he1, Real.rpow_neg_one]; ring
  · rw [← Real.rpow_two (x := K), ← Real.rpow_two (x := K ^ _), ← Real.rpow_mul hK.le]
    calc
      _ = (K ^ (2 : ℝ) * K ^ (-(2 * p - 1) / p * 2) / K ^ ((2 - p) / p)) / C := by ring
      _ = K ^ (2 + (-(2 * p - 1) / p) * 2 - (2 - p) / p) / C := by
        rw [Real.rpow_sub hK, Real.rpow_add hK]
      _ = 1 / (C * K) := by rw [he2, Real.rpow_neg_one]; ring

lemma weight_additive_absorption {t : Tuning} (ht : Valid t) {k : ℕ}
    (hk : k < iterations t) :
    accumulatedWeight t (k + 1) * pilotRadius t ^ 2 +
      20 * weight t k ^ t.p * pilotRadius t ^ t.p ≤ 1 / (2 * (iterations t : ℝ)) := by
  have hK : 0 < (iterations t : ℝ) := Nat.cast_pos.mpr (iterations_pos ht)
  have hD := weightScale_pos ht
  have hν := pilotRadius_pos ht
  have hp : 0 < t.p := by linarith [ht.exponent_gt]
  have hk' : (k : ℝ) + 1 ≤ (iterations t : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
  have ha : weight t k ≤ (iterations t : ℝ) / weightScale t := by
    exact div_le_div_of_nonneg_right hk' hD.le
  have hB : accumulatedWeight t (k + 1) ≤ (iterations t : ℝ) ^ 2 / weightScale t := by
    unfold accumulatedWeight
    push_cast
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ k + 1) hk'
    have hnum : ((k : ℝ) + 1) * (k + 1 + 1) ≤ 2 * (iterations t : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    calc
      _ ≤ (2 * (iterations t : ℝ) ^ 2) / (2 * weightScale t) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (iterations t : ℝ) ^ 2 / weightScale t := by ring
  have he := additive_products hp hK (by norm_num : (0 : ℝ) < 2 ^ 40)
  change ((iterations t : ℝ) / weightScale t) ^ t.p * pilotRadius t ^ t.p =
      1 / (((2 : ℝ) ^ 40) ^ t.p * (iterations t : ℝ)) ∧
    (iterations t : ℝ) ^ 2 / weightScale t * pilotRadius t ^ 2 =
      1 / ((2 : ℝ) ^ 40 * (iterations t : ℝ)) at he
  have h1 := mul_le_mul_of_nonneg_right hB (sq_nonneg (pilotRadius t))
  have h2 := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (weight_pos ht k).le ha hp.le) (Real.rpow_nonneg hν.le t.p)
  rw [he.2] at h1
  rw [he.1] at h2
  have hc := Real.self_le_rpow_of_one_le (by norm_num : (1 : ℝ) ≤ 2 ^ 40)
    (le_of_lt ht.exponent_gt)
  have hden := mul_le_mul_of_nonneg_right hc hK.le
  have hrec := one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ 40 * (iterations t : ℝ)) hden
  have hsmall : 21 / ((2 : ℝ) ^ 40 * (iterations t : ℝ)) ≤ 1 / (2 * (iterations t : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    norm_num
    linarith
  have h21 : 21 / ((2 : ℝ) ^ 40 * (iterations t : ℝ)) =
      1 / ((2 : ℝ) ^ 40 * (iterations t : ℝ)) +
      20 * (1 / ((2 : ℝ) ^ 40 * (iterations t : ℝ))) := by ring
  nlinarith only [h1, h2, hrec, hsmall, h21]

lemma noiseScale_nonneg {t : Tuning} (ht : Valid t) : 0 ≤ noiseScale t := by
  exact add_nonneg ht.noise_nonneg (div_nonneg ht.additive_nonneg (pilotRadius_pos ht).le)

lemma batchSize_pos {t : Tuning} (ht : Valid t) : 0 < batchSize t := by
  apply Nat.ceil_pos.mpr
  apply Real.rpow_pos_of_pos
  linarith [noiseScale_nonneg ht]

lemma pilotGroups_pos {t : Tuning} (ht : Valid t) : 0 < pilotGroups t := by
  apply Nat.ceil_pos.mpr
  have := conjugate_ge_two ht
  have := confidence_ge_one ht
  positivity

lemma sampleSize_pos {t : Tuning} (ht : Valid t) : 0 < sampleSize t :=
  Nat.mul_pos (batchSize_pos ht) (pilotGroups_pos ht)

lemma batch_power_lower {t : Tuning} (ht : Valid t) :
    (65536 * (1 + noiseScale t)) ^ t.p ≤ (batchSize t : ℝ) ^ (t.p - 1) := by
  have hx : 0 < 65536 * (1 + noiseScale t) := by linarith [noiseScale_nonneg ht]
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hx.le (conjugate t))
    (Nat.le_ceil ((65536 * (1 + noiseScale t)) ^ conjugate t)) (by linarith [ht.exponent_gt] : 0 ≤ t.p - 1)
  rw [← Real.rpow_mul hx.le] at h
  have he : conjugate t * (t.p - 1) = t.p := by
    unfold conjugate
    exact div_mul_cancel₀ _ (by linarith [ht.exponent_gt])
  rwa [he] at h

lemma batch_relative_moment {t : Tuning} (ht : Valid t) :
    6 / (batchSize t : ℝ) ^ (t.p - 1) * (noiseScale t) ^ t.p ≤ (1 / 192 : ℝ) ^ t.p / 16 := by
  have hp : 0 ≤ t.p := by linarith [ht.exponent_gt]
  have hσ := noiseScale_nonneg ht
  have hden : 0 < (batchSize t : ℝ) ^ (t.p - 1) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (batchSize_pos ht)) _
  have hbase : 96 * (192 * noiseScale t) ≤ 65536 * (1 + noiseScale t) := by nlinarith [noiseScale_nonneg ht]
  have hpow := Real.rpow_le_rpow (show 0 ≤ 96 * (192 * noiseScale t) by positivity) hbase hp
  rw [Real.mul_rpow (by norm_num) (by positivity),
    Real.mul_rpow (by norm_num) (noiseScale_nonneg ht)] at hpow
  have h96 := Real.self_le_rpow_of_one_le (by norm_num : (1 : ℝ) ≤ 96)
    (le_of_lt ht.exponent_gt)
  have hm := mul_le_mul_of_nonneg_right h96
    (show 0 ≤ (192 : ℝ) ^ t.p * (noiseScale t) ^ t.p by positivity)
  have hn := batch_power_lower ht
  have hfull : 96 * ((192 : ℝ) ^ t.p * (noiseScale t) ^ t.p) ≤
      (batchSize t : ℝ) ^ (t.p - 1) := hm.trans (hpow.trans hn)
  rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 192)]
  have h192 : 0 < (192 : ℝ) ^ t.p := Real.rpow_pos_of_pos (by norm_num) _
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  rw [← one_div]
  apply (le_div_iff₀ h192).mpr
  calc
    _ = (96 * ((192 : ℝ) ^ t.p * (noiseScale t) ^ t.p)) / (batchSize t : ℝ) ^ (t.p - 1) := by ring
    _ ≤ 1 := (div_le_one hden).mpr hfull

lemma sample_raw_moment {t : Tuning} (ht : Valid t) :
    6 / (sampleSize t : ℝ) ^ (t.p - 1) * (noiseScale t) ^ t.p ≤ 1 / 8 := by
  have hσ := noiseScale_nonneg ht
  have hn : batchSize t ≤ sampleSize t := by
    simpa only [sampleSize, Nat.mul_one] using
      Nat.mul_le_mul_left (batchSize t) (pilotGroups_pos ht)
  have hpow : (batchSize t : ℝ) ^ (t.p - 1) ≤ (sampleSize t : ℝ) ^ (t.p - 1) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by linarith [ht.exponent_gt])
  have hden : 0 < (batchSize t : ℝ) ^ (t.p - 1) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (batchSize_pos ht)) _
  have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6) hden hpow
  have hm := mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hσ t.p)
  have hb := batch_relative_moment ht
  have hc : (1 / 192 : ℝ) ^ t.p ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith [ht.exponent_gt])
  linarith

lemma iterations_power {t : Tuning} (ht : Valid t) :
    (2 : ℝ) ^ 48 * confidence t / t.ε ≤ (iterations t : ℝ) ^ ((3 * t.p - 2) / t.p) := by
  have hp : 0 < t.p := by linarith [ht.exponent_gt]
  have hd : 0 < 3 * t.p - 2 := by linarith [ht.exponent_gt]
  have hb : 0 < (2 : ℝ) ^ 48 * confidence t / t.ε := by
    have := confidence_ge_one ht
    have := ht.accuracy_pos
    positivity
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hb.le (t.p / (3 * t.p - 2)))
    (Nat.le_ceil (((2 : ℝ) ^ 48 * confidence t / t.ε) ^ (t.p / (3 * t.p - 2))))
    (div_pos hd hp).le
  rw [← Real.rpow_mul hb.le, show t.p / (3 * t.p - 2) * ((3 * t.p - 2) / t.p) = 1 by
      rw [← mul_div_assoc, div_mul_cancel₀ _ hd.ne', div_self hp.ne'],
    Real.rpow_one] at h
  exact h

lemma final_weight_lower {t : Tuning} (ht : Valid t) :
    (iterations t : ℝ) ^ ((3 * t.p - 2) / t.p) / (2 : ℝ) ^ 41 ≤
      accumulatedWeight t (iterations t) := by
  have hp : 0 < t.p := by linarith [ht.exponent_gt]
  have hK : 0 < (iterations t : ℝ) := Nat.cast_pos.mpr (iterations_pos ht)
  have hr : 0 < (iterations t : ℝ) ^ ((2 - t.p) / t.p) := Real.rpow_pos_of_pos hK _
  have he : (3 * t.p - 2) / t.p = 2 - (2 - t.p) / t.p := by field_simp; ring
  rw [he, Real.rpow_sub hK, Real.rpow_two]
  unfold accumulatedWeight weightScale
  apply (le_div_iff₀ (show 0 < 2 * ((2 : ℝ) ^ 40 * (iterations t : ℝ) ^ ((2 - t.p) / t.p)) by positivity)).mpr
  field_simp
  nlinarith

lemma final_accuracy {t : Tuning} (ht : Valid t) {gap : ℝ}
    (hgap : accumulatedWeight t (iterations t) * gap ≤ 16 * confidence t) : gap ≤ t.ε := by
  have hK := iterations_power ht
  have hA := final_weight_lower ht
  have hε := ht.accuracy_pos
  have hl := confidence_ge_one ht
  have hA0 : 0 < accumulatedWeight t (iterations t) := by
    have hk : 0 < (iterations t : ℝ) := Nat.cast_pos.mpr (iterations_pos ht)
    exact lt_of_lt_of_le (by positivity) hA
  have h1 := mul_le_mul_of_nonneg_right hK hε.le
  have h2 := mul_le_mul_of_nonneg_right hA hε.le
  have he : ((2 : ℝ) ^ 48 * confidence t / t.ε) * t.ε = (2 : ℝ) ^ 48 * confidence t :=
    div_mul_cancel₀ _ hε.ne'
  rw [he] at h1
  norm_num at h1 h2
  nlinarith

end LongTails.Proofs.AffineMomentParameters
