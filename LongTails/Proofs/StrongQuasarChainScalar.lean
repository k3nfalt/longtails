import LongTails.Proofs.StrongQuasarChainBlock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open intervalIntegral

namespace LongTails.Proofs.StrongQuasarChainScalar

open LongTails.Proofs.StrongQuasarChainBlock LongTails.Proofs.FiniteSumNondualLowerGeometry

lemma deadEnergy_eq (θ t : ℝ) : deadEnergy θ t = deadZone θ t ^ 2 / 2 := rfl

lemma deadSlope_eq (θ t : ℝ) (hθ : 0 ≤ θ) : deadSlope θ t = softThreshold θ t := by
  unfold deadSlope softThreshold
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma dead_model (θ x y : ℝ) (hθ : 0 ≤ θ) :
    0 ≤ deadEnergy θ y - deadEnergy θ x - deadSlope θ x * (y - x) ∧
      deadEnergy θ y - deadEnergy θ x - deadSlope θ x * (y - x) ≤ (y - x) ^ 2 / 2 := by
  have h := deadZone_quadratic_model θ x y hθ
  rw [deadEnergy_eq, deadEnergy_eq, deadSlope_eq θ x hθ]
  constructor <;> linarith [h.1, h.2]

lemma dead_lipschitz (θ x y : ℝ) (hθ : 0 ≤ θ) :
    |deadSlope θ x - deadSlope θ y| ≤ |x - y| := by
  rw [deadSlope_eq θ x hθ, deadSlope_eq θ y hθ]
  exact softThreshold_lipschitz θ x y hθ

lemma dead_inactive {θ t : ℝ} (hθ : 0 ≤ θ) (h : |t| ≤ θ) :
    deadEnergy θ t = 0 ∧ deadSlope θ t = 0 := by
  have h2 := deadZone_inactive θ t h
  rw [deadEnergy_eq, deadSlope_eq θ t hθ, h2.1, h2.2]
  norm_num

noncomputable def bumpSlope (v : ℝ) : ℝ := gain v * (v - 1)

noncomputable def bump (v : ℝ) : ℝ := ∫ s in (1 : ℝ)..v, bumpSlope s

lemma gain_continuous : Continuous gain := by
  unfold gain
  fun_prop

lemma bumpSlope_continuous : Continuous bumpSlope := by
  unfold bumpSlope
  exact gain_continuous.mul (continuous_id.sub continuous_const)

lemma bump_hasDerivAt (v : ℝ) : HasDerivAt bump (bumpSlope v) v :=
  (bumpSlope_continuous.integral_hasStrictDerivAt 1 v).hasDerivAt

lemma gain_zero_of_small {v : ℝ} (h : |v| ≤ 1 / 16) : gain v = 0 := by
  unfold gain
  rw [max_eq_left (by linarith)]
  exact min_eq_right (by norm_num)

lemma bumpSlope_zero_of_small {v : ℝ} (h : |v| ≤ 1 / 16) : bumpSlope v = 0 := by
  rw [bumpSlope, gain_zero_of_small h, zero_mul]

lemma bumpSlope_mul_nonneg (v : ℝ) : 0 ≤ bumpSlope v * (v - 1) := by
  unfold bumpSlope
  have := gain_nonneg v
  have : 0 ≤ (v - 1) ^ 2 := sq_nonneg _
  nlinarith

lemma clamp_lipschitz (a b : ℝ) : |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [abs_le]
  constructor <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

lemma gain_lipschitz (v w : ℝ) : |gain v - gain w| ≤ 16 * |v - w| := by
  unfold gain
  have h := clamp_lipschitz (16 * |v| - 1) (16 * |w| - 1)
  have he : (16 * |v| - 1) - (16 * |w| - 1) = 16 * (|v| - |w|) := by ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
  have := abs_abs_sub_abs_le v w
  linarith

lemma gain_one_of_large {v : ℝ} (h : 1 / 8 ≤ |v|) : gain v = 1 := gain_eq_one h

lemma bumpSlope_lipschitz (v w : ℝ) : |bumpSlope v - bumpSlope w| ≤ 19 * |v - w| := by
  unfold bumpSlope
  have hg := gain_lipschitz v w
  have hg0 := gain_nonneg v
  have hg1 := gain_le_one v
  have hw0 := gain_nonneg w
  have hw1 := gain_le_one w
  by_cases hv : 1 / 8 ≤ |v|
  · by_cases hw : 1 / 8 ≤ |w|
    · rw [gain_eq_one hv, gain_eq_one hw]
      have : (1 : ℝ) * (v - 1) - 1 * (w - 1) = v - w := by ring
      rw [this]
      linarith [abs_nonneg (v - w)]
    · push Not at hw
      have hw' := abs_lt.mp hw
      have he : gain v * (v - 1) - gain w * (w - 1) =
          gain v * (v - w) + (gain v - gain w) * (w - 1) := by ring
      rw [he]
      have hb : |w - 1| ≤ 9 / 8 := by rw [abs_le]; constructor <;> linarith
      calc |gain v * (v - w) + (gain v - gain w) * (w - 1)|
          ≤ |gain v * (v - w)| + |(gain v - gain w) * (w - 1)| := abs_add_le _ _
        _ = gain v * |v - w| + |gain v - gain w| * |w - 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hg0]
        _ ≤ 1 * |v - w| + (16 * |v - w|) * (9 / 8) := by
          gcongr
        _ = 19 * |v - w| := by ring
  · push Not at hv
    have hv' := abs_lt.mp hv
    have he : gain v * (v - 1) - gain w * (w - 1) =
        gain w * (v - w) + (gain v - gain w) * (v - 1) := by ring
    rw [he]
    have hb : |v - 1| ≤ 9 / 8 := by rw [abs_le]; constructor <;> linarith
    calc |gain w * (v - w) + (gain v - gain w) * (v - 1)|
        ≤ |gain w * (v - w)| + |(gain v - gain w) * (v - 1)| := abs_add_le _ _
      _ = gain w * |v - w| + |gain v - gain w| * |v - 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hw0]
      _ ≤ 1 * |v - w| + (16 * |v - w|) * (9 / 8) := by
        gcongr
      _ = 19 * |v - w| := by ring

lemma bump_sub (x y : ℝ) : bump y - bump x = ∫ s in x..y, bumpSlope s := by
  unfold bump
  rw [integral_interval_sub_left (bumpSlope_continuous.intervalIntegrable _ _)
    (bumpSlope_continuous.intervalIntegrable _ _)]

lemma bump_remainder (x y : ℝ) :
    |bump y - bump x - bumpSlope x * (y - x)| ≤ 10 * (y - x) ^ 2 := by
  rw [bump_sub]
  have hc : (∫ s in x..y, bumpSlope s) - bumpSlope x * (y - x) =
      ∫ s in x..y, (bumpSlope s - bumpSlope x) := by
    rw [integral_sub (bumpSlope_continuous.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hc]
  rcases le_total x y with hxy | hxy
  · have h1 := abs_integral_le_integral_abs (f := fun s => bumpSlope s - bumpSlope x)
      (μ := MeasureTheory.volume) hxy
    have h2 : ∫ s in x..y, |bumpSlope s - bumpSlope x| ≤ ∫ s in x..y, 19 * (s - x) := by
      apply integral_mono_on hxy
      · exact ((bumpSlope_continuous.sub continuous_const).abs).intervalIntegrable _ _
      · exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
      · intro s hs
        show |bumpSlope s - bumpSlope x| ≤ 19 * (s - x)
        have := bumpSlope_lipschitz s x
        rw [abs_of_nonneg (by linarith [hs.1] : 0 ≤ s - x)] at this
        exact this
    have h3 : ∫ s in x..y, 19 * (s - x) = 19 * ((y - x) ^ 2 / 2) := by
      rw [integral_const_mul, integral_sub intervalIntegrable_id intervalIntegrable_const,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring
    have : 0 ≤ (y - x) ^ 2 := sq_nonneg _
    linarith
  · rw [integral_symm, abs_neg]
    have h1 := abs_integral_le_integral_abs (f := fun s => bumpSlope s - bumpSlope x)
      (μ := MeasureTheory.volume) hxy
    have h2 : ∫ s in y..x, |bumpSlope s - bumpSlope x| ≤ ∫ s in y..x, 19 * (x - s) := by
      apply integral_mono_on hxy
      · exact ((bumpSlope_continuous.sub continuous_const).abs).intervalIntegrable _ _
      · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
      · intro s hs
        show |bumpSlope s - bumpSlope x| ≤ 19 * (x - s)
        have := bumpSlope_lipschitz s x
        rw [abs_of_nonpos (by linarith [hs.2] : s - x ≤ 0)] at this
        linarith
    have h3 : ∫ s in y..x, 19 * (x - s) = 19 * ((y - x) ^ 2 / 2) := by
      rw [integral_const_mul, integral_sub intervalIntegrable_const intervalIntegrable_id,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring
    have : 0 ≤ (y - x) ^ 2 := sq_nonneg _
    linarith

lemma bump_bounds (v : ℝ) : 0 ≤ bump v ∧ bump v ≤ (v - 1) ^ 2 / 2 := by
  unfold bump
  rcases le_total 1 v with h | h
  · constructor
    · apply integral_nonneg h
      intro s hs
      unfold bumpSlope
      have := gain_nonneg s
      nlinarith [hs.1]
    · have h2 : ∫ s in (1 : ℝ)..v, bumpSlope s ≤ ∫ s in (1 : ℝ)..v, (s - 1) := by
        apply integral_mono_on h (bumpSlope_continuous.intervalIntegrable _ _)
          ((continuous_id.sub continuous_const).intervalIntegrable _ _)
        intro s hs
        show bumpSlope s ≤ s - 1
        unfold bumpSlope
        have := gain_le_one s
        nlinarith [hs.1]
      have h3 : ∫ s in (1 : ℝ)..v, (s - 1) = (v - 1) ^ 2 / 2 := by
        rw [integral_sub intervalIntegrable_id intervalIntegrable_const, integral_id,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      linarith
  · rw [integral_symm]
    constructor
    · have : ∫ s in v..(1 : ℝ), bumpSlope s ≤ 0 := by
        have h0 : ∫ s in v..(1 : ℝ), bumpSlope s ≤ ∫ s in v..(1 : ℝ), (0 : ℝ) := by
          apply integral_mono_on h (bumpSlope_continuous.intervalIntegrable _ _)
            intervalIntegrable_const
          intro s hs
          unfold bumpSlope
          have := gain_nonneg s
          nlinarith [hs.2]
        simpa using h0
      linarith
    · have h2 : ∫ s in v..(1 : ℝ), (s - 1) ≤ ∫ s in v..(1 : ℝ), bumpSlope s := by
        apply integral_mono_on h ((continuous_id.sub continuous_const).intervalIntegrable _ _)
          (bumpSlope_continuous.intervalIntegrable _ _)
        intro s hs
        show s - 1 ≤ bumpSlope s
        unfold bumpSlope
        have := gain_le_one s
        have := gain_nonneg s
        nlinarith [hs.2]
      have h3 : ∫ s in v..(1 : ℝ), (s - 1) = -((v - 1) ^ 2 / 2) := by
        rw [integral_sub intervalIntegrable_id intervalIntegrable_const, integral_id,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      linarith

lemma bump_flat {v : ℝ} (h : |v| ≤ 1 / 16) : bump v = bump 0 := by
  have hs := bump_sub 0 v
  have hz : ∫ s in (0 : ℝ)..v, bumpSlope s = 0 := by
    have : ∫ s in (0 : ℝ)..v, bumpSlope s = ∫ s in (0 : ℝ)..v, (0 : ℝ) := by
      apply integral_congr
      intro s hs
      apply bumpSlope_zero_of_small
      rw [Set.uIcc] at hs
      have h1 := hs.1
      have h2 := hs.2
      have hv := abs_le.mp h
      rw [abs_le]
      constructor
      · have : min 0 v ≥ -(1 / 16) := le_min (by norm_num) hv.1
        linarith
      · have : max 0 v ≤ 1 / 16 := max_le (by norm_num) hv.2
        linarith
    rw [this]
    simp
  linarith

lemma bump_zero_lower : 49 / 128 ≤ bump 0 := by
  unfold bump
  rw [integral_symm]
  have hsplit := integral_add_adjacent_intervals
    (bumpSlope_continuous.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) (1 / 8))
    (bumpSlope_continuous.intervalIntegrable (μ := MeasureTheory.volume) (1 / 8 : ℝ) 1)
  have hA : ∫ s in (0 : ℝ)..(1 / 8), bumpSlope s ≤ 0 := by
    have h0 : ∫ s in (0 : ℝ)..(1 / 8), bumpSlope s ≤ ∫ s in (0 : ℝ)..(1 / 8), (0 : ℝ) := by
      apply integral_mono_on (by norm_num) (bumpSlope_continuous.intervalIntegrable _ _)
        intervalIntegrable_const
      intro s hs
      unfold bumpSlope
      have := gain_nonneg s
      nlinarith [hs.2]
    simpa using h0
  have hB : ∫ s in (1 / 8 : ℝ)..1, bumpSlope s = ∫ s in (1 / 8 : ℝ)..1, (s - 1) := by
    apply integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    unfold bumpSlope
    rw [gain_eq_one (by rw [abs_of_nonneg (by linarith [hs.1])]; exact hs.1), one_mul]
  have hC : ∫ s in (1 / 8 : ℝ)..1, (s - 1) = -(49 / 128) := by
    rw [integral_sub intervalIntegrable_id intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  linarith

end LongTails.Proofs.StrongQuasarChainScalar
