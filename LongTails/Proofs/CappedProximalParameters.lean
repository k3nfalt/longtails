import LongTails.Algorithms.CappedProximal
import LongTails.Proofs.CappedProximalGeometry

namespace LongTails.Proofs.CappedProximalParameters

open LongTails.Setups.CappedHessianSimilarConvex
open LongTails.Algorithms.CappedProximal

lemma outer_regularization_pos {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    0 < outerRegularization p := by
  exact add_pos_of_pos_of_nonneg hm (div_nonneg hd (Real.sqrt_nonneg _))

lemma subproblem_convexity_pos {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    0 < subproblemConvexity p := add_pos hm (outer_regularization_pos hm hd)

lemma epoch_length_lower (p : Params) :
    1 + 64 * Real.sqrt (p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p) +
      2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) ≤ (epochLength p : ℝ) := by
  exact Nat.le_ceil _

lemma epoch_length_pos {p : Params} (hs : 0 < p.s) : 0 < epochLength p := by
  have hb := epoch_length_lower p
  have hn : 0 ≤ 2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) := by positivity
  have hr := Real.sqrt_nonneg (p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p)
  have ht : 0 < (epochLength p : ℝ) := by linarith
  exact_mod_cast ht

lemma inner_regularization_pos {p : Params} (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    0 < innerRegularization p := by
  have hq := subproblem_convexity_pos hm hd
  have ht : 0 < (epochLength p : ℝ) := by exact_mod_cast epoch_length_pos hs
  dsimp [innerRegularization]
  positivity

lemma inner_regularization_lower {p : Params} (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    64 * (p.δ * (1 + Real.sqrt p.m / p.s)) ≤ innerRegularization p := by
  have hs' : 0 < (p.s : ℝ) := by exact_mod_cast hs
  have hq := subproblem_convexity_pos hm hd
  let d := p.δ * (1 + Real.sqrt p.m / p.s)
  have hd' : 0 ≤ d := by dsimp [d]; positivity
  have hn : 0 ≤ 2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) := by positivity
  have hb := epoch_length_lower p
  have ht : 64 * Real.sqrt (d / subproblemConvexity p) ≤ (epochLength p : ℝ) := by
    dsimp [d]
    linarith
  have hroot := Real.sq_sqrt (div_nonneg hd' hq.le)
  have hsquare : 4096 * (d / subproblemConvexity p) ≤ (epochLength p : ℝ) ^ 2 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ 64 * Real.sqrt (d / subproblemConvexity p) by positivity) ht 2
    nlinarith only [hp, hroot]
  have hmul := mul_le_mul_of_nonneg_left hsquare hq.le
  have he : subproblemConvexity p * (d / subproblemConvexity p) = d := by field_simp
  change 64 * d ≤ subproblemConvexity p * (epochLength p : ℝ) ^ 2 / 64
  nlinarith only [hmul, he]

lemma inner_regularization_threshold {p : Params} (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    16 * p.δ + 6 * (Real.sqrt p.m * p.δ) / p.s ≤ innerRegularization p := by
  have hl := inner_regularization_lower hs hm hd
  have hn : 0 ≤ (Real.sqrt p.m * p.δ) / p.s := by positivity
  have he : p.δ * (1 + Real.sqrt p.m / p.s) = p.δ + (Real.sqrt p.m * p.δ) / p.s := by ring
  rw [he] at hl
  simp only [div_eq_mul_inv] at hl hn ⊢
  nlinarith

lemma inner_variance_weight_bound {p : Params} (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    (4 * p.δ ^ 2 / (p.s * innerRegularization p)) * (epochLength p : ℝ) ^ 3 /
      innerRegularization p ≤ 1 / 64 := by
  have hs' : 0 < (p.s : ℝ) := by exact_mod_cast hs
  have hq := subproblem_convexity_pos hm hd
  have ht : 0 < (epochLength p : ℝ) := by exact_mod_cast epoch_length_pos hs
  have hb := epoch_length_lower p
  have hr := Real.sqrt_nonneg (p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p)
  have hn : 2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) ≤
      (epochLength p : ℝ) := by linarith
  have hmul := (div_le_iff₀ (show 0 < (p.s : ℝ) * subproblemConvexity p ^ 2 by positivity)).mp hn
  have he : (4 * p.δ ^ 2 / (p.s * innerRegularization p)) * (epochLength p : ℝ) ^ 3 /
      innerRegularization p =
      16384 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2 * (epochLength p : ℝ)) := by
    dsimp [innerRegularization]
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (show 0 < (p.s : ℝ) * subproblemConvexity p ^ 2 * (epochLength p : ℝ) by positivity)).2
  norm_num at hmul
  nlinarith only [hmul]

lemma outer_length_lower (p : Params) :
    8 * Real.sqrt (outerRegularization p / p.μ) ≤ (outerLength p : ℝ) := Nat.le_ceil _

lemma outer_length_pos {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) : 0 < outerLength p := by
  have hr := outer_regularization_pos hm hd
  have hs := Real.sqrt_pos.mpr (div_pos hr hm)
  have hb := outer_length_lower p
  have ht : 0 < (outerLength p : ℝ) := by linarith
  exact_mod_cast ht

lemma eighth_power_ceil {X : ℝ} (hx : 0 < X) :
    (1 / 8 : ℝ) ^ ⌈Real.log X / Real.log 8⌉₊ ≤ 1 / X := by
  let k := ⌈Real.log X / Real.log 8⌉₊
  have hlog : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  have hk : Real.log X ≤ (k : ℝ) * Real.log 8 := (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have hi : Real.log (1 / 8 : ℝ) = -Real.log 8 := by rw [one_div, Real.log_inv]
  have he : Real.exp ((k : ℝ) * Real.log (1 / 8 : ℝ)) ≤ Real.exp (-Real.log X) := by
    apply Real.exp_le_exp.mpr
    rw [hi]
    linarith
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 8),
    Real.exp_neg, Real.exp_log hx] at he
  simpa only [one_div] using he

lemma solve_error_bound {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (solveLength p - 1) ≤
      outerRegularization p / (2 ^ 20 * subproblemConvexity p * (outerLength p : ℝ) ^ 4) := by
  have hr := outer_regularization_pos hm hd
  have hq := subproblem_convexity_pos hm hd
  have hk : 0 < (outerLength p : ℝ) := by exact_mod_cast outer_length_pos hm hd
  let X := 2 ^ 20 * subproblemConvexity p * (outerLength p : ℝ) ^ 4 / outerRegularization p
  have hx : 0 < X := by dsimp [X]; positivity
  have he := eighth_power_ceil hx
  have hn : 0 ≤ (1 / 8 : ℝ) ^ ⌈Real.log X / Real.log 8⌉₊ := by positivity
  have hleft : solveLength p - 1 = ⌈Real.log X / Real.log 8⌉₊ := by
    simp only [solveLength, Nat.add_sub_cancel_left, X]
  rw [hleft]
  have hi : 1 / X = outerRegularization p /
      (2 ^ 20 * subproblemConvexity p * (outerLength p : ℝ) ^ 4) := by
    dsimp [X]
    field_simp
  rw [← hi]
  linarith

lemma outer_error_coefficient {rho q K beta : ℝ} (hr : 0 < rho) (hq : 0 < q)
    (hK : 1 ≤ K) (hb : 0 ≤ beta) (hqr : rho ≤ q)
    (hbeta : beta ≤ rho / (2 ^ 20 * q * K ^ 4)) :
    let theta := 1 / (1024 * K ^ 2)
    8 * q * beta * (K ^ 3 / rho) + rho * (theta + 8 * beta / theta) * (K ^ 2 / rho) ≤ 1 / 4 := by
  have hK0 : 0 < K := by linarith
  have hp := (le_div_iff₀ (show 0 < 2 ^ 20 * q * K ^ 4 by positivity)).mp hbeta
  norm_num at hp
  have hbsmall : 1048576 * beta * K ^ 4 ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hq).mp
    nlinarith only [hp, hqr]
  have hkpow : K ^ 3 ≤ K ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (pow_nonneg hK0.le 3)]
  have hm := mul_le_mul_of_nonneg_left hkpow (mul_nonneg hq.le hb)
  have hfirst : 8 * q * beta * (K ^ 3 / rho) ≤ 1 / 131072 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hr).2
    nlinarith only [hp, hm]
  have he :
      8 * q * beta * (K ^ 3 / rho) +
        rho * (1 / (1024 * K ^ 2) + 8 * beta / (1 / (1024 * K ^ 2))) * (K ^ 2 / rho) =
      8 * q * beta * (K ^ 3 / rho) + 1 / 1024 + 8192 * beta * K ^ 4 := by
    field_simp
    ring
  dsimp only
  rw [he]
  nlinarith only [hfirst, hbsmall]

lemma outer_accuracy_scale {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    4 * outerRegularization p / (outerLength p : ℝ) ^ 2 ≤ p.μ / 16 := by
  have hr := outer_regularization_pos hm hd
  have hk : 0 < (outerLength p : ℝ) := by exact_mod_cast outer_length_pos hm hd
  have hroot := Real.sq_sqrt (div_nonneg hr.le hm.le)
  have hs := pow_le_pow_left₀
    (show 0 ≤ 8 * Real.sqrt (outerRegularization p / p.μ) by positivity) (outer_length_lower p) 2
  have hsq : 64 * (outerRegularization p / p.μ) ≤ (outerLength p : ℝ) ^ 2 := by
    nlinarith only [hroot, hs]
  have hh := mul_le_mul_of_nonneg_left hsq hm.le
  have he : p.μ * (outerRegularization p / p.μ) = outerRegularization p := by field_simp
  apply (div_le_iff₀ (sq_pos_of_pos hk)).2
  nlinarith only [hh, he]

lemma restart_accuracy {p : Params} (hD : 0 ≤ p.Δ) (he : 0 < p.ε) :
    (1 / 8 : ℝ) ^ restartCount p * p.Δ ≤ p.ε := by
  have hx : 0 < 2 + p.Δ / p.ε := by positivity
  have hb := mul_le_mul_of_nonneg_right (eighth_power_ceil hx) hD
  have hfrac : 1 / (2 + p.Δ / p.ε) * p.Δ ≤ p.ε := by
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ hx).2
    have hid : p.ε * (2 + p.Δ / p.ε) = 2 * p.ε + p.Δ := by
      field_simp
    rw [hid]
    linarith
  have hp : 0 ≤ (1 / 8 : ℝ) ^ ⌈Real.log (2 + p.Δ / p.ε) / Real.log 8⌉₊ * p.Δ := by positivity
  dsimp only [restartCount]
  rw [pow_add, pow_one]
  nlinarith only [hb, hfrac, hp]

end LongTails.Proofs.CappedProximalParameters
