import LongTails.Proofs.SurjectiveProxLinearModel

namespace LongTails.Proofs.SurjectiveProxLinearTuning

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearModel

lemma eta_le_quarter (p : Params) (hp : spec.valid p) : eta p ≤ 1 / 4 := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hγ : 1 ≤ gamma p := by
    unfold gamma
    have hprod : 0 ≤ rho p * p.m * p.H := by positivity
    linarith
  have hden : 0 < 4 * gamma p := by positivity
  unfold eta
  apply (div_le_iff₀ hden).mpr
  nlinarith

lemma sensitivity_coefficients {H M ρ η : ℝ}
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 8 * H ^ 2)
    (_hη : 0 ≤ η) (hηmax : η ≤ 1 / 4) :
    η * (1 + H ^ 4) ≤ 16 * M * H ^ 6 ∧
    η * (ρ * M + H ^ 3 * (H + 2 * H * (ρ * M))) ≤ 16 * M * H ^ 6 ∧
    H ^ 3 ≤ 16 * M * H ^ 6 ∧ H ^ 3 * (ρ * M) ≤ 16 * M * H ^ 6 := by
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  have h16 : (1 : ℝ) ≤ H ^ 6 := one_le_pow₀ hH
  have h26 : H ^ 2 ≤ H ^ 6 := pow_le_pow_right₀ hH (by norm_num)
  have h36 : H ^ 3 ≤ H ^ 6 := pow_le_pow_right₀ hH (by norm_num)
  have h46 : H ^ 4 ≤ H ^ 6 := pow_le_pow_right₀ hH (by norm_num)
  have h56 : H ^ 5 ≤ H ^ 6 := pow_le_pow_right₀ hH (by norm_num)
  have hR : H ^ 6 ≤ M * H ^ 6 := by nlinarith [pow_nonneg hH0 6]
  have hr : ρ * M ≤ 8 * M * H ^ 6 := by
    have hh := mul_le_mul_of_nonneg_right hρmax hM0
    have hq := mul_le_mul_of_nonneg_left h26 (show 0 ≤ 8 * M by positivity)
    nlinarith
  have hr4 : 2 * H ^ 4 * (ρ * M) ≤ 16 * M * H ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left hρmax (show 0 ≤ 2 * H ^ 4 * M by positivity)
    nlinarith
  have hr3 : H ^ 3 * (ρ * M) ≤ 8 * M * H ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left hρmax (show 0 ≤ H ^ 3 * M by positivity)
    have hq := mul_le_mul_of_nonneg_left h56 (show 0 ≤ 8 * M by positivity)
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hηmax (show 0 ≤ 1 + H ^ 4 by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hηmax
    (show 0 ≤ ρ * M + H ^ 3 * (H + 2 * H * (ρ * M)) by positivity)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

lemma parameter_sensitivity_coefficients (p : Params) (hp : spec.valid p) :
    eta p * (1 + p.H ^ 4) ≤ 16 * p.m * p.H ^ 6 ∧
    eta p * (rho p * p.m + p.H ^ 3 * (p.H + 2 * p.H * (rho p * p.m))) ≤
      16 * p.m * p.H ^ 6 ∧
    p.H ^ 3 ≤ 16 * p.m * p.H ^ 6 ∧
    p.H ^ 3 * (rho p * p.m) ≤ 16 * p.m * p.H ^ 6 := by
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast hp.1
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hρmax : rho p ≤ 8 * p.H ^ 2 := by
    unfold rho
    nlinarith [mul_nonneg hH (sub_nonneg.mpr hp.2.1)]
  exact sensitivity_coefficients hp.2.1 hm (valid_tuning_positive p hp).1.le hρmax
    (valid_tuning_positive p hp).2.2.1.le (eta_le_quarter p hp)

lemma four_term_square {a b c d : ℝ} :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

lemma variance_scales_positive (p : Params) (hp : spec.valid p) :
    0 < sensitivity p ∧ 0 < radius p ∧ 0 < certificateError p ∧
      0 < beta p ∧ beta p ≤ 1 ∧ 0 < relaxation p := by
  have hm : (0 : ℝ) < p.m := Nat.cast_pos.mpr hp.1
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one hp.2.1
  have hσ := hp.2.2.1
  have hε := hp.2.2.2.2.1
  have hC : 0 < sensitivity p := by unfold sensitivity; positivity
  have hr : 0 < radius p := by unfold radius; positivity
  have he : 0 < certificateError p := by unfold certificateError; positivity
  have hbden : 0 < 1 + 32768 * sensitivity p * p.σ ^ 2 / radius p ^ 2 := by positivity
  have hb : 0 < beta p := by unfold beta; positivity
  have hb1 : beta p ≤ 1 := by
    unfold beta
    apply (div_le_one hbden).mpr
    have hnon : 0 ≤ 32768 * sensitivity p * p.σ ^ 2 / radius p ^ 2 := by positivity
    linarith
  have hθ : 0 < relaxation p := by unfold relaxation; positivity
  exact ⟨hC, hr, he, hb, hb1, hθ⟩

lemma relaxation_le_tenth (p : Params) (hp : spec.valid p) : relaxation p ≤ 1 / 10 := by
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast hp.1
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hH7 : 1 ≤ p.H ^ 7 := one_le_pow₀ hp.2.1
  have hσ := hp.2.2.1
  have hε := hp.2.2.2.2.1
  have hu : 0 ≤ 524288 * p.m ^ 2 * p.H ^ 9 * p.σ / p.ε := by positivity
  have hprod : 1 ≤ (p.m : ℝ) * p.H ^ 7 := one_le_mul_of_one_le_of_one_le hm hH7
  have hden : 512 ≤ 512 * p.m * p.H ^ 7 *
      (1 + 524288 * p.m ^ 2 * p.H ^ 9 * p.σ / p.ε) := by
    have hn := mul_nonneg (show 0 ≤ 512 * p.m * p.H ^ 7 by positivity) hu
    nlinarith
  unfold relaxation
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 512) hden)).mpr
  nlinarith

lemma initialBatch_pos (p : Params) : 0 < initialBatch p := by unfold initialBatch; omega

lemma certificateBatch_pos (p : Params) : 0 < certificateBatch p := by unfold certificateBatch; omega

lemma variance_absorption (p : Params) (hp : spec.valid p) :
    relaxation p ^ 2 * sensitivity p * p.H ^ 2 / beta p ≤ 1 / 256 := by
  have hm : (0 : ℝ) < p.m := Nat.cast_pos.mpr hp.1
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one hp.2.1
  have hσ := hp.2.2.1
  have hε := hp.2.2.2.2.1
  let u : ℝ := 524288 * p.m ^ 2 * p.H ^ 9 * p.σ / p.ε
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : 0 < 1 + u := by positivity
  have hid : relaxation p ^ 2 * sensitivity p * p.H ^ 2 / beta p =
      (1 + u ^ 2 / 2) / (256 * (1 + u) ^ 2) := by
    dsimp [relaxation, sensitivity, beta, radius, u]
    field_simp [hε.ne', hm.ne', hH.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ (show 0 < 256 * (1 + u) ^ 2 by positivity)).mpr
  nlinarith [sq_nonneg u]

lemma ridge_scale_identity (p : Params) (hp : spec.valid p) :
    65536 * sensitivity p * ridge p ^ 2 = radius p ^ 2 := by
  have hm : (p.m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.1).ne'
  have hH : p.H ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.2.1).ne'
  unfold sensitivity ridge radius
  field_simp [hm, hH]
  ring

lemma variance_noise_bound (p : Params) (hp : spec.valid p) :
    32768 * sensitivity p * beta p * p.σ ^ 2 ≤ radius p ^ 2 := by
  have h := variance_scales_positive p hp
  have hr := h.2.1
  have hb := h.2.2.2.1.le
  have hC := h.1
  have hden : 0 < 1 + 32768 * sensitivity p * p.σ ^ 2 / radius p ^ 2 := by positivity
  have hunit : beta p * (1 + 32768 * sensitivity p * p.σ ^ 2 / radius p ^ 2) = 1 := by
    unfold beta
    exact one_div_mul_cancel hden.ne'
  have hid : beta p * (radius p ^ 2 + 32768 * sensitivity p * p.σ ^ 2) = radius p ^ 2 := by
    calc
      _ = (beta p * (1 + 32768 * sensitivity p * p.σ ^ 2 / radius p ^ 2)) * radius p ^ 2 := by
        field_simp [hr.ne']
      _ = _ := by rw [hunit, one_mul]
  nlinarith [mul_nonneg hb (sq_nonneg (radius p))]

lemma initial_variance_scale (p : Params) (hp : spec.valid p) :
    1024 * sensitivity p * (p.σ ^ 2 / initialBatch p) ≤ radius p ^ 2 := by
  have hr := (variance_scales_positive p hp).2.1
  have hB : (0 : ℝ) < initialBatch p := Nat.cast_pos.mpr (initialBatch_pos p)
  have hceil := Nat.le_ceil (1024 * sensitivity p * p.σ ^ 2 / radius p ^ 2)
  have hlarge : 1024 * sensitivity p * p.σ ^ 2 / radius p ^ 2 ≤ (initialBatch p : ℝ) := by
    unfold initialBatch
    push_cast
    linarith
  have hmul := (div_le_iff₀ (sq_pos_of_pos hr)).mp hlarge
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hB).mpr
  nlinarith

lemma iteration_horizon (p : Params) :
    1024 * p.Δ / (gamma p * relaxation p * radius p ^ 2) + 64 / beta p ≤
      ((iterations p + 1 : ℕ) : ℝ) := by
  have h := Nat.le_ceil (1024 * p.Δ / (gamma p * relaxation p * radius p ^ 2) + 64 / beta p)
  unfold iterations
  push_cast
  linarith

end LongTails.Proofs.SurjectiveProxLinearTuning
