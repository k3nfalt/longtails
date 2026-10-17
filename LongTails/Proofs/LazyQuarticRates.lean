import LongTails.Proofs.LazyQuarticStageParameters
import LongTails.Proofs.LazyQuarticCurvature

namespace LongTails.Proofs.LazyQuarticRates

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric

lemma condition_power (p : Params) (hp : spec.valid p) {r : ℝ} :
    (condition p) ^ r ≤ (2 : ℝ) ^ (24 * r) +
      p.Δ ^ (r / 2) * p.L₃ ^ (r / 6) / p.ε ^ (2 * r / 3) := by
  have hb := LazyQuarticParameters.beta_pos p hp
  have hL := hp.1
  have hΔ := hp.2.1
  have hε := hp.2.2.2
  have hc : 0 < (p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have ht : 0 ≤ p.Δ ^ (r / 2) * p.L₃ ^ (r / 6) / p.ε ^ (2 * r / 3) := by positivity
  have hpow : (beta p / ((p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ))) ^ r =
      p.Δ ^ (r / 2) * p.L₃ ^ (r / 6) / p.ε ^ (2 * r / 3) := by
    rw [Real.div_rpow hb.le hc.le, beta, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (mul_pos hL hΔ).le, Real.mul_rpow hL.le hΔ.le,
      ← Real.rpow_mul (show 0 ≤ p.L₃ * p.ε ^ 2 by positivity),
      Real.mul_rpow hL.le (sq_nonneg _), ← Real.rpow_natCast_mul hε.le]
    have he : (1 / 2 : ℝ) * r = r / 6 + (1 / 3 : ℝ) * r := by ring
    rw [he, Real.rpow_add hL]
    field_simp
    ring_nf
  by_cases hh : beta p / 2 ^ 24 ≤ (p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ)
  · have hk : condition p = (2 : ℝ) ^ 24 := by
      unfold condition alpha
      rw [min_eq_left hh]
      field_simp
    rw [hk, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_add_of_nonneg_right ht
  · have hk : condition p = beta p / ((p.L₃ * p.ε ^ 2) ^ (1 / 3 : ℝ)) := by
      unfold condition alpha
      rw [min_eq_right (le_of_not_ge hh)]
    rw [hk, hpow]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num) _)

lemma log_lower (p : Params) (hp : spec.valid p) : (1 : ℝ) / 2 ≤ Real.log (logarithmArgument p) := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (LazyQuarticParameters.logarithmArgument_ge_two p hp)
  norm_num at hh
  linarith

lemma innerSteps_upper (p : Params) (hp : spec.valid p) :
    (innerSteps p : ℝ) ≤ 4096 * Real.sqrt (condition p) * Real.log (logarithmArgument p) := by
  have hΔ := hp.2.1
  have hL := hp.1
  have hε := hp.2.2.2
  have hk := LazyQuarticParameters.condition_lower p hp
  have hs : 1 ≤ Real.sqrt (condition p) := (Real.le_sqrt (by norm_num) (by norm_num at hk; linarith)).mpr (by norm_num at hk ⊢; linarith)
  have hl := log_lower p hp
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 11 * Real.sqrt (condition p) * Real.log (logarithmArgument p) by positivity)
  change (innerSteps p : ℝ) < _ at hh
  have hm := mul_le_mul hs hl (by norm_num) (Real.sqrt_nonneg _)
  norm_num at hh hm
  nlinarith

lemma ordinary_bound (p : Params) (hp : spec.valid p) :
    (1 + (2 * innerSteps p + 8) * stages p : ℕ) ≤
      ⌈2 ^ 90 * (1 + p.Δ ^ (5 / 4 : ℝ) * p.L₃ ^ (5 / 12 : ℝ) / p.ε ^ (5 / 3 : ℝ)) *
        Real.log (logarithmArgument p)⌉₊ := by
  have hΔ := hp.2.1
  have hL := hp.1
  have hε := hp.2.2.2
  have hk := LazyQuarticParameters.condition_lower p hp
  have hkpos : 0 < condition p := by norm_num at hk; linarith
  have hs : 1 ≤ Real.sqrt (condition p) := (Real.le_sqrt (by norm_num) (by norm_num at hk; linarith)).mpr (by norm_num at hk ⊢; linarith)
  have hl := log_lower p hp
  have hn := innerSteps_upper p hp
  have hT := LazyQuarticCurvature.stages_upper p hp
  have hm := mul_le_mul hs hl (by norm_num) (Real.sqrt_nonneg _)
  have hN : 2 * (innerSteps p : ℝ) + 8 ≤ 16384 * Real.sqrt (condition p) * Real.log (logarithmArgument p) := by nlinarith
  have hprod := mul_le_mul hN hT (Nat.cast_nonneg (stages p)) (by positivity)
  have hid : Real.sqrt (condition p) * condition p ^ 2 = condition p ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hkpos]
    norm_num
  have hrate := condition_power p hp (r := (5 / 2 : ℝ))
  norm_num at hrate
  have hmul := mul_le_mul_of_nonneg_right hrate (show 0 ≤ 2 ^ 26 * Real.log (logarithmArgument p) by positivity)
  have hmain : (1 + (2 * innerSteps p + 8) * stages p : ℕ) ≤
      ⌈2 ^ 90 * (1 + p.Δ ^ (5 / 4 : ℝ) * p.L₃ ^ (5 / 12 : ℝ) / p.ε ^ (5 / 3 : ℝ)) * Real.log (logarithmArgument p)⌉₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    apply le_trans ?_ (Nat.le_ceil _)
    push_cast
    have he : 16384 * Real.sqrt (condition p) * Real.log (logarithmArgument p) * (2 ^ 12 * condition p ^ 2) =
        2 ^ 26 * condition p ^ (5 / 2 : ℝ) * Real.log (logarithmArgument p) := by rw [← hid]; ring
    rw [he] at hprod
    have hnon : 0 ≤ p.Δ ^ (5 / 4 : ℝ) * p.L₃ ^ (5 / 12 : ℝ) / p.ε ^ (5 / 3 : ℝ) := by positivity
    have hnonlog := mul_nonneg hnon (show 0 ≤ Real.log (logarithmArgument p) by linarith)
    norm_num at hprod hmul ⊢
    nlinarith only [hprod, hmul, hl, hnonlog]
  exact hmain

end LongTails.Proofs.LazyQuarticRates
