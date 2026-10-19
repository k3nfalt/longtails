import LongTails.Proofs.CharacteristicGradientBounds
import LongTails.Proofs.ClippedExtragradientBudget

open MeasureTheory

namespace LongTails.Proofs.CharacteristicTuning

open LongTails.Setups.QuantileSymmetricRemainderConvex
open LongTails.Algorithms.CharacteristicGradient

lemma scale_pos (q : Params) (hv : spec.valid q) : 0 < scale q := by
  rcases hv with ⟨hd, hL, hR, hr, hM, he⟩
  unfold scale
  positivity

lemma shape_nonneg (q : Params) (hv : spec.valid q) : 0 ≤ shape q := by
  rcases hv with ⟨hd, hL, hR, hr, hM, he⟩
  unfold shape
  positivity

lemma scale_shape (q : Params) (hv : spec.valid q) :
    Real.sqrt q.d * q.R * scale q / q.ε = 8 * shape q := by
  have he := hv.2.2.2.2.2.ne'
  have hs := Real.sq_sqrt (Nat.cast_nonneg q.d : (0 : ℝ) ≤ q.d)
  unfold scale shape
  field_simp
  ring_nf
  rw [hs]
  ring

lemma frequency_quantile (q : Params) (hv : spec.valid q) :
    (1 / scale q) * (2 * q.L * q.R + q.r) ≤ 1 / 4 := by
  have hH := scale_pos q hv
  have hG : 0 ≤ 2 * q.L * q.R + q.r := by
    rcases hv with ⟨_, hL, hR, hr, _, _⟩
    positivity
  have hn : 0 ≤ 64 * Real.sqrt q.d * q.M * q.R / q.ε := by
    rcases hv with ⟨_, _, hR, _, hM, he⟩
    positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hH]
  unfold scale
  linarith

lemma remainder_bias (q : Params) (hv : spec.valid q) :
    Real.sqrt q.d * q.M / scale q ≤ q.ε / (64 * q.R) := by
  have hH := scale_pos q hv
  have hR := hv.2.2.1
  have he := hv.2.2.2.2.2
  have hG : 0 ≤ 8 * (2 * q.L * q.R + q.r) := by
    have hL := hv.2.1
    have hr := hv.2.2.2.1
    positivity
  apply (div_le_div_iff₀ hH (by positivity)).mpr
  unfold scale
  field_simp
  nlinarith

lemma batch_decay (q : Params) (hv : spec.valid q) :
    512 * shape q ≤ (2 : ℝ) ^ batchCount q := by
  have hs := shape_nonneg q hv
  have h := OracleTemplate.ClippedExtragradient.dyadic_count_covers (u := 16 * shape q) (by positivity)
  unfold batchCount
  rw [pow_add]
  norm_num only [pow_one] at *
  have he : 32 * (16 * shape q) = 512 * shape q := by ring
  rw [he] at h
  nlinarith

lemma truncation_bias (q : Params) (hv : spec.valid q) :
    Real.sqrt q.d * (1 / 2 : ℝ) ^ batchCount q * scale q ≤ q.ε / (64 * q.R) := by
  have hR := hv.2.2.1
  have he := hv.2.2.2.2.2
  have hs := scale_shape q hv
  have hk := batch_decay q hv
  have heq : Real.sqrt q.d * q.R * scale q = 8 * shape q * q.ε :=
    (div_eq_iff he.ne').mp hs
  have hb : 64 * (Real.sqrt q.d * q.R * scale q) ≤
      q.ε * (2 : ℝ) ^ batchCount q := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hk he.le]
  rw [one_div_pow, mul_one_div, div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [hb]

lemma rate_algebra {L R e H n D d b : ℝ} (hL : 0 ≤ L) (_hR : 0 ≤ R)
    (he : 0 < e) (hn : 0 < n) (hD : 0 < D) (_hd : 0 ≤ d)
    (hdef : D = 2 * L + 64 * n * d * H ^ 2 / e)
    (hdet : 16 * L * R ^ 2 ≤ e * n ^ 2)
    (hnoise : 512 * d * H ^ 2 * R ^ 2 ≤ e ^ 2 * n)
    (hb : 4 * R * b ≤ e / 8) :
    2 * D * R ^ 2 / (n * (n + 1)) + 4 * R * b + 4 * n * (4 * d * H ^ 2) / D ≤ e := by
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hfirst : 4 * L * R ^ 2 / n ^ 2 ≤ e / 4 := by
    rw [div_le_iff₀ hn2]
    nlinarith
  have hsecond : 128 * d * H ^ 2 * R ^ 2 / (e * n) ≤ e / 4 := by
    rw [div_le_iff₀ (mul_pos he hn)]
    nlinarith
  have hsplit : 2 * D * R ^ 2 / n ^ 2 =
      4 * L * R ^ 2 / n ^ 2 + 128 * d * H ^ 2 * R ^ 2 / (e * n) := by
    rw [hdef]
    field_simp
    ring
  have hmain : 2 * D * R ^ 2 / (n * (n + 1)) ≤ e / 2 := by
    calc
      _ ≤ 2 * D * R ^ 2 / n ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) hn2
        nlinarith
      _ ≤ e / 2 := by rw [hsplit]; linarith
  have hstoch : 4 * n * (4 * d * H ^ 2) / D ≤ e / 4 := by
    rw [div_le_iff₀ hD, hdef]
    have hcancel : e * (64 * n * d * H ^ 2 / e) = 64 * n * d * H ^ 2 :=
      mul_div_cancel₀ _ he.ne'
    nlinarith [mul_nonneg he.le hL]
  linarith

lemma iteration_bounds (q : Params) :
    0 < iterationCount q ∧
    4 * Real.sqrt (q.L * q.R ^ 2 / q.ε) ≤ (iterationCount q : ℝ) ∧
    32768 * (shape q) ^ 2 ≤ (iterationCount q : ℝ) := by
  have hc := Nat.le_ceil (4 * Real.sqrt (q.L * q.R ^ 2 / q.ε) + 32768 * (shape q) ^ 2)
  refine ⟨by unfold iterationCount; omega, ?_, ?_⟩ <;>
    unfold iterationCount <;> push_cast <;> nlinarith [Real.sqrt_nonneg (q.L * q.R ^ 2 / q.ε), sq_nonneg (shape q)]

lemma curvature_bounds (q : Params) (hv : spec.valid q) :
    0 < curvature q ∧ 2 * q.L ≤ curvature q := by
  rcases hv with ⟨_, hL, hR, hr, hM, he⟩
  have hn : 0 ≤ 64 * iterationCount q * q.d * scale q ^ 2 / q.ε := by positivity
  unfold curvature
  constructor <;> linarith

lemma tuned_rate (q : Params) (hv : spec.valid q) :
    2 * curvature q * q.R ^ 2 / ((iterationCount q : ℝ) * ((iterationCount q : ℝ) + 1)) +
      4 * q.R * (Real.sqrt q.d * (q.M * (1 / scale q) +
        (1 / 2 : ℝ) ^ batchCount q / (1 / scale q))) +
      4 * iterationCount q * (4 * q.d / (1 / scale q) ^ 2) / curvature q ≤ q.ε := by
  have hL := hv.2.1
  have hR := hv.2.2.1
  have he := hv.2.2.2.2.2
  have hH := scale_pos q hv
  have hn := iteration_bounds q
  have hsn := Real.sqrt_nonneg (q.L * q.R ^ 2 / q.ε)
  have hs := Real.sq_sqrt (show 0 ≤ q.L * q.R ^ 2 / q.ε by positivity)
  have hdet : 16 * q.L * q.R ^ 2 ≤ q.ε * (iterationCount q : ℝ) ^ 2 := by
    have hb : 16 * (q.L * q.R ^ 2 / q.ε) ≤ (iterationCount q : ℝ) ^ 2 := by nlinarith [hn.2.1]
    have hh := (div_le_iff₀ he).mp (show (16 * q.L * q.R ^ 2) / q.ε ≤ (iterationCount q : ℝ) ^ 2 by simpa only [mul_div_assoc, mul_assoc] using hb)
    nlinarith
  have heq := (div_eq_iff he.ne').mp (scale_shape q hv)
  have hsq : (q.d : ℝ) * q.R ^ 2 * scale q ^ 2 = 64 * shape q ^ 2 * q.ε ^ 2 := by
    have h := congrArg (fun a : ℝ => a ^ 2) heq
    have hd := Real.sq_sqrt (Nat.cast_nonneg q.d : (0 : ℝ) ≤ q.d)
    simpa only [mul_pow, hd, show (8 : ℝ) ^ 2 = 64 by norm_num] using h
  have hnoise : 512 * (q.d : ℝ) * scale q ^ 2 * q.R ^ 2 ≤ q.ε ^ 2 * iterationCount q := by
    have hh := mul_le_mul_of_nonneg_right hn.2.2 (sq_nonneg q.ε)
    nlinarith [hsq]
  have hb : 4 * q.R * (Real.sqrt q.d * (q.M * (1 / scale q) +
      (1 / 2 : ℝ) ^ batchCount q / (1 / scale q))) ≤ q.ε / 8 := by
    have h1 := (le_div_iff₀ (show 0 < 64 * q.R by positivity)).mp (remainder_bias q hv)
    have h2 := (le_div_iff₀ (show 0 < 64 * q.R by positivity)).mp (truncation_bias q hv)
    have hsplit : Real.sqrt q.d * (q.M * (1 / scale q) +
        (1 / 2 : ℝ) ^ batchCount q / (1 / scale q)) =
        Real.sqrt q.d * q.M / scale q + Real.sqrt q.d * (1 / 2 : ℝ) ^ batchCount q * scale q := by
      field_simp
    rw [hsplit]
    nlinarith
  have h := rate_algebra hL.le hR.le he (Nat.cast_pos.mpr hn.1)
    (curvature_bounds q hv).1 (Nat.cast_nonneg q.d) rfl hdet hnoise hb
  convert h using 1
  simp

end LongTails.Proofs.CharacteristicTuning
