import LongTails.Algorithms.CompositeLazyCubic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace LongTails.Proofs.CompositeCurvatureParameters

open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Algorithms.CompositeLazyCubic

lemma cubicCoefficient_pos (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m) :
    0 < cubicCoefficient p := by
  have hm0 : (0 : ℝ) < p.m := by exact_mod_cast (by omega : 0 < p.m)
  exact div_pos hH (pow_pos hm0 3)

lemma localHessianLip_pos (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m) :
    0 < localHessianLip p := by
  have hg := cubicCoefficient_pos p hH hm
  dsimp [localHessianLip]
  positivity

lemma depth_two_le (p : Params) : 2 ≤ depth p := by simp [depth]

lemma condition_lt_pow_depth (p : Params) : condition p < (2 : ℝ) ^ (depth p - 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (p.m ^ 3 + 4)
  rw [← Nat.log2_eq_log_two] at h
  have he : depth p - 1 = (Nat.log2 (p.m ^ 3 + 4)).succ := by simp [depth]; omega
  rw [he]
  dsimp [condition]
  exact_mod_cast h

lemma condition_bounds (p : Params) (hm : 1 ≤ p.m) :
    1 ≤ condition p ∧ condition p ≤ 5 * (p.m : ℝ) ^ 3 := by
  have hm' : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hpow : (1 : ℝ) ≤ (p.m : ℝ) ^ 3 := one_le_pow₀ hm'
  dsimp [condition]
  constructor <;> nlinarith

lemma factor_bounds (p : Params) : 1 ≤ extrapolationFactor p ∧ extrapolationFactor p ≤ 2 := by
  have hJ : (1 : ℝ) ≤ depth p := by exact_mod_cast (le_trans (by omega) (depth_two_le p))
  have hpos : (0 : ℝ) < depth p := by linarith
  have hi : (depth p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hJ
  have hi0 := inv_nonneg.mpr hpos.le
  dsimp [extrapolationFactor]
  constructor <;> linarith

lemma factor_power_bounds (p : Params) :
    2 ≤ extrapolationFactor p ^ depth p ∧ extrapolationFactor p ^ depth p ≤ 3 := by
  have hJ : 0 < depth p := lt_of_lt_of_le (by norm_num) (depth_two_le p)
  have hJr : (0 : ℝ) < depth p := Nat.cast_pos.mpr hJ
  constructor
  · have h := one_add_mul_le_pow (a := (depth p : ℝ)⁻¹) (by have hi := inv_pos.mpr hJr; linarith) (depth p)
    norm_num [extrapolationFactor, hJr.ne'] at h ⊢
    exact h
  · have h := Real.add_one_le_exp ((depth p : ℝ)⁻¹)
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (depth p : ℝ)⁻¹)
      (by simpa [add_comm] using h) (depth p)
    have he : (Real.exp ((depth p : ℝ)⁻¹)) ^ depth p = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      exact mul_inv_cancel₀ hJr.ne'
    change (1 + (depth p : ℝ)⁻¹) ^ depth p ≤ 3
    exact hp.trans (he.le.trans Real.exp_one_lt_three.le)

lemma local_condition_identity (p : Params) (hm : 1 ≤ p.m) :
    localHessianLip p = cubicCoefficient p * condition p := by
  have hm0 : (p.m : ℝ) ≠ 0 := by exact_mod_cast (by omega : p.m ≠ 0)
  dsimp [localHessianLip, cubicCoefficient, condition]
  field_simp

lemma hessian_weight_bound (p : Params) (i : ℕ) :
    0 ≤ (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ (2 * i) ∧
    (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ (2 * i) ≤ (1 / 16 : ℝ) ^ i := by
  have hc := factor_bounds p
  have hc0 : 0 ≤ extrapolationFactor p := by linarith
  constructor
  · positivity
  · rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith

lemma third_weight_bound (p : Params) (i : ℕ) :
    (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ (3 * i) ≤ (1 / 8 : ℝ) ^ i := by
  have hc := factor_bounds p
  have hc0 : 0 ≤ extrapolationFactor p := by linarith
  have hc3 := pow_le_pow_left₀ hc0 hc.2 3
  rw [pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  norm_num at hc3
  linarith

lemma scale_bounds (p : Params) : 1 ≤ regularizerScale p ∧ regularizerScale p ≤ 2 := by
  have hc := factor_bounds p
  have hc0 : 0 ≤ extrapolationFactor p := by linarith
  have hw : ∀ i, 0 ≤ (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ i := by
    intro i; positivity
  constructor
  · have h := Finset.single_le_sum (s := Finset.range (depth p + 1))
      (fun i _ => hw i) (by simp : 0 ∈ Finset.range (depth p + 1))
    simpa [regularizerScale] using h
  · have hpoint : ∀ i ∈ Finset.range (depth p + 1),
        (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ i ≤ (1 / 32 : ℝ) ^ i := by
      intro i _
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      linarith [hc.2]
    have hsum := Finset.sum_le_sum hpoint
    have hg : (∑ i ∈ Finset.range (depth p + 1), (1 / 32 : ℝ) ^ i) ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 32 : ℝ) ≠ 1)]
      apply (div_le_iff_of_neg (by norm_num : (1 / 32 : ℝ) - 1 < 0)).mpr
      have hh := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 32) (depth p + 1)
      linarith
    exact hsum.trans hg

lemma search_exponent (p : Params) : 48 + 5 * depth p ≤ searchIterations p := by
  simp only [searchIterations]
  omega

lemma depth_linear_bound (p : Params) : (depth p : ℝ) + 1 ≤ (2 : ℝ) ^ depth p := by
  exact_mod_cast (Nat.succ_le_of_lt (show depth p < 2 ^ depth p from Nat.lt_two_pow_self))

lemma search_direction_bound (p : Params) :
    (225 : ℝ) * 2 ^ 40 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 ≤ 2 ^ searchIterations p := by
  have hj := depth_linear_bound p
  have hκ : condition p ≤ (2 : ℝ) ^ depth p :=
    (condition_lt_pow_depth p).le.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  have hj0 : 0 ≤ (depth p : ℝ) + 1 := by positivity
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hκ0 : 0 ≤ condition p := by dsimp [condition]; positivity
  have hκ3 := pow_le_pow_left₀ hκ0 hκ 3
  have hprod := mul_le_mul hj2 hκ3 (pow_nonneg hκ0 3)
    (sq_nonneg ((2 : ℝ) ^ depth p))
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (search_exponent p)
  have he : ((2 : ℝ) ^ depth p) ^ 2 * ((2 : ℝ) ^ depth p) ^ 3 = 2 ^ (5 * depth p) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he] at hprod
  rw [pow_add] at hpow
  have hs := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 225 * 2 ^ 40)
  have hn : 0 ≤ (2 : ℝ) ^ (5 * depth p) := by positivity
  nlinarith only [hs, hpow, hn]

lemma search_resolution {p : Params} {D Δ : ℝ} (hD : 0 ≤ D) (hΔ : 0 ≤ Δ)
    (hbound : D ^ 2 ≤ (2 : ℝ) ^ 40 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ) :
    (9 / 4 : ℝ) * D ^ 2 / 2 ^ searchIterations p ≤ Δ / 100 ∧
      D / 2 ^ searchIterations p ≤ Real.sqrt Δ / 2 := by
  have hp : 0 < (2 : ℝ) ^ searchIterations p := by positivity
  have hp1 : 1 ≤ (2 : ℝ) ^ searchIterations p := one_le_pow₀ (by norm_num)
  have ht := mul_le_mul_of_nonneg_right (search_direction_bound p) hΔ
  have hs := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 225)
  have h225 : 225 * D ^ 2 ≤ (2 : ℝ) ^ searchIterations p * Δ := by nlinarith only [ht, hs]
  constructor
  · apply (div_le_iff₀ hp).mpr
    nlinarith only [h225]
  · apply (sq_le_sq₀ (div_nonneg hD hp.le) (div_nonneg (Real.sqrt_nonneg Δ) (by norm_num))).mp
    rw [div_pow, div_pow, Real.sq_sqrt hΔ]
    norm_num
    apply (div_le_iff₀ (pow_pos hp 2)).mpr
    have hh : (2 : ℝ) ^ searchIterations p ≤ ((2 : ℝ) ^ searchIterations p) ^ 2 := by nlinarith only [hp1]
    have hhΔ := mul_le_mul_of_nonneg_right hh hΔ
    nlinarith only [h225, hhΔ, sq_nonneg D]

lemma m_sq_condition_cube (p : Params) (hm : 1 ≤ p.m) : (p.m : ℝ) ^ 2 ≤ condition p ^ 3 := by
  have hm1 : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hp : (p.m : ℝ) ^ 2 ≤ (p.m : ℝ) ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
  have hκ := (condition_bounds p hm).1
  have hκ3 : condition p ≤ condition p ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hκ (by norm_num : 1 ≤ 3)
  have hbase : (p.m : ℝ) ^ 2 ≤ condition p := by dsimp [condition]; linarith
  exact hbase.trans hκ3

lemma innerIterations_sq (p : Params) :
    (innerIterations p : ℝ) ^ 2 = 1073741824 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 := by
  simp only [innerIterations, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

lemma innerIterations_pos (p : Params) (hm : 1 ≤ p.m) : 0 < innerIterations p := by
  have hm0 : 0 < p.m := by omega
  unfold innerIterations
  positivity

lemma inner_direction_scalar {p : Params} {A V X U D F Fu offset Δ : ℝ}
    (hm : 1 ≤ p.m) (hΔ : 0 ≤ Δ) (hA : 0 ≤ A) (hAN : A ≤ (innerIterations p : ℝ) ^ 2)
    (hF : offset ≤ F) (hFu : Fu - offset ≤ 2 * Δ)
    (henergy : A * (F - Fu) + V / 2 ≤
      131072 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 * Δ / 2 + A * (Δ / 100))
    (hX : X ≤ 153000 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ)
    (hU : U ≤ 131072 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 * Δ)
    (hD : D ≤ 2 * V + 4 * X + 4 * U) :
    D ≤ (2 : ℝ) ^ 40 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ := by
  have hgap : -2 * Δ ≤ F - Fu := by linarith
  have hmul := mul_le_mul_of_nonneg_left hgap hA
  have hV : V ≤ 131072 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 * Δ + 5 * A * Δ := by
    have hn := mul_nonneg hA hΔ
    nlinarith only [henergy, hmul, hn]
  have hANΔ := mul_le_mul_of_nonneg_right hAN hΔ
  rw [innerIterations_sq] at hANΔ
  have hκ := mul_le_mul_of_nonneg_right (m_sq_condition_cube p hm)
    (by positivity : 0 ≤ ((depth p : ℝ) + 1) ^ 2 * Δ)
  have hn : 0 ≤ ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ := by
    have hκ0 : 0 ≤ condition p := (condition_bounds p hm).1.trans' zero_le_one
    positivity
  norm_num at hD ⊢
  nlinarith only [hD, hV, hX, hU, hANΔ, hκ, hn]

lemma inner_accuracy {p : Params} {gap V Δ : ℝ} (hm : 1 ≤ p.m) (hΔ : 0 ≤ Δ) (hV : 0 ≤ V)
    (henergy : ((innerIterations p : ℝ) * ((innerIterations p : ℝ) + 1) / 4) * gap + V ≤
      131072 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 * Δ / 2 +
        ((innerIterations p : ℝ) * ((innerIterations p : ℝ) + 1) / 4) * (Δ / 100)) :
    gap ≤ Δ / 12 := by
  have hN : 0 < (innerIterations p : ℝ) := Nat.cast_pos.mpr (innerIterations_pos p hm)
  have hA : 0 < (innerIterations p : ℝ) * ((innerIterations p : ℝ) + 1) / 4 := by positivity
  have hden : (innerIterations p : ℝ) ^ 2 ≤ (innerIterations p : ℝ) * ((innerIterations p : ℝ) + 1) := by nlinarith only [hN]
  have hscaled := mul_le_mul_of_nonneg_right hden hΔ
  rw [innerIterations_sq] at hscaled
  have hn : 0 ≤ (innerIterations p : ℝ) * ((innerIterations p : ℝ) + 1) * Δ := by positivity
  apply le_of_mul_le_mul_left (a := (innerIterations p : ℝ) * ((innerIterations p : ℝ) + 1) / 4) ?_ hA
  nlinarith only [henergy, hV, hscaled, hn]

lemma gap_contraction_bound (p : Params) (hm : 1 ≤ p.m) :
    (3 / 4 : ℝ) ^ gapIterations p * condition p ^ 2 ≤ (1 / 2 : ℝ) ^ 14 := by
  have hJ := depth_two_le p
  have hS : 3 * (2 * depth p + 14) ≤ gapIterations p := by dsimp [gapIterations]; omega
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1) hS
  have hstep : (3 / 4 : ℝ) ^ gapIterations p ≤ (1 / 2 : ℝ) ^ (2 * depth p + 14) := by
    apply hp.trans
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num : (3 / 4 : ℝ) ^ 3 ≤ 1 / 2) _
  have hκ : condition p ≤ (2 : ℝ) ^ depth p :=
    (condition_lt_pow_depth p).le.trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
  have hκ0 : 0 ≤ condition p := (condition_bounds p hm).1.trans' zero_le_one
  have hκ2 := pow_le_pow_left₀ hκ0 hκ 2
  have hprod := mul_le_mul hstep hκ2 (sq_nonneg (condition p))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
  have he : (1 / 2 : ℝ) ^ (2 * depth p) * (2 : ℝ) ^ (2 * depth p) = 1 := by
    rw [← mul_pow]; norm_num
  have heq : (1 / 2 : ℝ) ^ (2 * depth p + 14) * ((2 : ℝ) ^ depth p) ^ 2 = (1 / 2 : ℝ) ^ 14 := by
    rw [pow_add, ← pow_mul, Nat.mul_comm (depth p) 2]
    calc
      _ = ((1 / 2 : ℝ) ^ (2 * depth p) * 2 ^ (2 * depth p)) * (1 / 2 : ℝ) ^ 14 := by ring
      _ = _ := by rw [he, one_mul]
  exact hprod.trans_eq heq

lemma cubic_calls_bound (p : Params) (hm : 1 ≤ p.m) :
    cubicSolveCalls p ≤ 2 ^ 35 * p.m * (depth p + 1) ^ 4 := by
  let t := depth p + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have ht1 : t ≤ t ^ 4 := by simpa using pow_le_pow_right₀ ht (by norm_num : 1 ≤ 4)
  have ht2 : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht (by norm_num : 2 ≤ 4)
  have ht3 : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ ht (by norm_num : 3 ≤ 4)
  have hm2 := Nat.mul_le_mul_left p.m ht2
  have hm3 := Nat.mul_le_mul_left p.m ht3
  have hmt := Nat.mul_le_mul_right (t ^ 4) hm
  have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht
  have he : cubicSolveCalls p =
      2147483648 * p.m * t ^ 4 + 1107296256 * p.m * t ^ 3 +
      16777216 * p.m * t ^ 2 + 256 * t + 12 := by
    dsimp [cubicSolveCalls, gapEpochCalls, trialCalls, searchIterations, innerIterations, gapIterations, t]
    ring
  rw [he]
  change _ ≤ 2 ^ 35 * p.m * t ^ 4
  norm_num
  nlinarith only [hm2, hm3, hmt, ht4, ht1]

lemma cubic_hessians_bound (p : Params) : gapIterations p + 3 ≤ 260 * (depth p + 1) := by
  dsimp [gapIterations]
  omega

lemma outerCoefficient_pos (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m)
    (hR : 0 < p.R) (hε : 0 < p.ε) : 0 < outerCoefficient p := by
  have hγ := cubicCoefficient_pos p hH hm
  dsimp only [outerCoefficient]
  positivity

lemma scaledGap_eq (p : Params) : scaledGap p = cubicCoefficient p * p.R ^ 3 / p.ε := by
  dsimp only [scaledGap, cubicCoefficient]
  ring

lemma scaledGap_pos (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m)
    (hR : 0 < p.R) (hε : 0 < p.ε) : 0 < scaledGap p := by
  rw [scaledGap_eq]
  have hγ := cubicCoefficient_pos p hH hm
  positivity

lemma outer_tuning_identity (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m)
    (hR : 0 < p.R) (hε : 0 < p.ε) :
    outerCoefficient p * p.R ^ 2 / p.ε = scaledGap p ^ (4 / 7 : ℝ) := by
  have hγ := cubicCoefficient_pos p hH hm
  have hr : p.R ^ (2 / 7 : ℝ) * p.R ^ (12 / 7 : ℝ) = p.R ^ 2 := by
    rw [← Real.rpow_add hR]
    norm_num
  have he : p.ε ^ (3 / 7 : ℝ) * p.ε ^ (4 / 7 : ℝ) = p.ε := by
    rw [← Real.rpow_add hε]
    norm_num
  have hr3 : (p.R ^ 3) ^ (4 / 7 : ℝ) = p.R ^ (12 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  rw [scaledGap_eq, Real.div_rpow (by positivity) hε.le, Real.mul_rpow hγ.le (by positivity), hr3]
  change (cubicCoefficient p ^ (4 / 7 : ℝ) * p.ε ^ (3 / 7 : ℝ) / p.R ^ (2 / 7 : ℝ)) * p.R ^ 2 / p.ε = _
  calc
    _ = (cubicCoefficient p ^ (4 / 7 : ℝ) * p.ε ^ (3 / 7 : ℝ) / p.R ^ (2 / 7 : ℝ)) *
        (p.R ^ (2 / 7 : ℝ) * p.R ^ (12 / 7 : ℝ)) /
        (p.ε ^ (3 / 7 : ℝ) * p.ε ^ (4 / 7 : ℝ)) := by rw [hr, he]
    _ = _ := by
      have hrp : p.R ^ (2 / 7 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
      have hep : p.ε ^ (3 / 7 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
      field_simp

lemma outer_rate_square (p : Params) (hq : 0 ≤ scaledGap p) :
    (scaledGap p ^ (2 / 7 : ℝ)) ^ 2 = scaledGap p ^ (4 / 7 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num

lemma outer_rate_seventh (p : Params) (hq : 0 ≤ scaledGap p) :
    (scaledGap p ^ (2 / 7 : ℝ)) ^ 7 = scaledGap p ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num

lemma outer_tuning_cube (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m)
    (hR : 0 < p.R) (hε : 0 < p.ε) :
    outerCoefficient p ^ 2 * (scaledGap p ^ (2 / 7 : ℝ)) ^ 3 = cubicCoefficient p ^ 2 * p.R ^ 2 := by
  have hq := scaledGap_pos p hH hm hR hε
  have hid := outer_tuning_identity p hH hm hR hε
  rw [← outer_rate_square p hq.le] at hid
  have he : outerCoefficient p = (scaledGap p ^ (2 / 7 : ℝ)) ^ 2 * p.ε / p.R ^ 2 := by
    apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hR))).mpr
    exact (div_eq_iff hε.ne').mp hid
  rw [he]
  calc
    _ = (scaledGap p ^ (2 / 7 : ℝ)) ^ 7 * p.ε ^ 2 / p.R ^ 4 := by ring
    _ = scaledGap p ^ 2 * p.ε ^ 2 / p.R ^ 4 := by rw [outer_rate_seventh p hq.le]
    _ = _ := by rw [scaledGap_eq]; field_simp

lemma outer_dyadic_cover (p : Params) (hH : 0 < p.H) (hm : 1 ≤ p.m)
    (hR : 0 < p.R) (hε : 0 < p.ε) :
    outerCoefficient p * (p.R ^ 2 / p.ε) ≤
      (2 : ℝ) ^ (Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊) + 1) := by
  rw [← mul_div_assoc, outer_tuning_identity p hH hm hR hε]
  have hc := Nat.le_ceil (scaledGap p ^ (4 / 7 : ℝ))
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊)
  rw [← Nat.log2_eq_log_two] at hp
  have hp' : (2 : ℝ) + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊ <
      (2 : ℝ) ^ (Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊) + 1) := by exact_mod_cast hp
  linarith

lemma outer_horizon_exceeds (p : Params) (hq : 0 ≤ scaledGap p) :
    (2 + 4 * ((Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊) : ℝ) + 2)) *
      scaledGap p ^ (2 / 7 : ℝ) < (outerIterations p : ℝ) := by
  have hv : 0 ≤ scaledGap p ^ (2 / 7 : ℝ) := Real.rpow_nonneg hq _
  have hceil := Nat.le_ceil (scaledGap p ^ (2 / 7 : ℝ))
  have hL : 0 ≤ (Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊) : ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hceil (by positivity :
    0 ≤ 16 * (3 + (Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊) : ℝ)))
  dsimp only [outerIterations]
  push_cast
  nlinarith only [hm, hL, hv, mul_nonneg hL hv]

lemma total_calls_bound (p : Params) (hm : 1 ≤ p.m) :
    cubicSolveCalls p * outerIterations p ≤ 2 ^ 39 * p.m * (3 + Nat.log2 (p.m ^ 3 + 4)) ^ 4 *
      (3 + Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊)) * (1 + ⌈scaledGap p ^ (2 / 7 : ℝ)⌉₊) := by
  have h := Nat.mul_le_mul_right (outerIterations p) (cubic_calls_bound p hm)
  convert h using 1
  dsimp only [outerIterations, depth]
  ring

lemma total_hessians_bound (p : Params) :
    (gapIterations p + 3) * outerIterations p ≤ 4160 * (3 + Nat.log2 (p.m ^ 3 + 4)) *
      (3 + Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊)) * (1 + ⌈scaledGap p ^ (2 / 7 : ℝ)⌉₊) := by
  have h := Nat.mul_le_mul_right (outerIterations p) (cubic_hessians_bound p)
  convert h using 1
  dsimp only [outerIterations, depth]
  ring

end LongTails.Proofs.CompositeCurvatureParameters
