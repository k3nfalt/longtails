import LongTails.Proofs.SurjectiveProxLinearTuning

namespace LongTails.Proofs.SurjectiveProxLinearCertificateTuning

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearTuning
open LongTails.Proofs.SurjectiveProxLinearModel

lemma basic_scale_bounds (p : Params) (hp : spec.valid p) :
    rho p ≤ 8 * p.H ^ 2 ∧ gamma p ≤ 10 * p.m * p.H ^ 3 ∧
    certificateError p ≤ radius p ∧ 16 * p.H ^ 4 * ridge p ≤ radius p ∧
    64 * p.m * p.H ^ 3 * radius p = p.ε := by
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast hp.1
  have hH := hp.2.1
  have hHp : 0 < p.H := lt_of_lt_of_le zero_lt_one hH
  have hmp : (0 : ℝ) < p.m := lt_of_lt_of_le zero_lt_one hm
  have hε := hp.2.2.2.2.1
  have hH2 : p.H ≤ p.H ^ 2 := by nlinarith
  have hH3 : p.H ^ 2 ≤ p.H ^ 3 := by nlinarith [mul_nonneg (sq_nonneg p.H) (sub_nonneg.mpr hH)]
  have hmH3 : p.H ^ 3 ≤ p.m * p.H ^ 3 := by nlinarith
  have hrho : rho p ≤ 8 * p.H ^ 2 := by unfold rho; nlinarith
  have hgamma : gamma p ≤ 10 * p.m * p.H ^ 3 := by
    have hr := mul_le_mul_of_nonneg_right hrho (show 0 ≤ (p.m : ℝ) * p.H by positivity)
    unfold gamma
    nlinarith
  refine ⟨hrho, hgamma, ?_, ?_, ?_⟩
  · unfold certificateError radius
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    have hH6 : 1 ≤ p.H ^ 6 := one_le_pow₀ hH
    have hprod : 1 ≤ (p.m : ℝ) * p.H ^ 6 := one_le_mul_of_one_le_of_one_le hm hH6
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 64 * (p.m : ℝ) * p.H ^ 3 by positivity)
    nlinarith
  · have hid : 16 * p.H ^ 4 * ridge p = radius p / (512 * p.m * p.H ^ 2) := by
      unfold ridge radius
      field_simp [hHp.ne', hmp.ne']
      ring
    rw [hid]
    apply div_le_self (variance_scales_positive p hp).2.1.le
    have hpow : 1 ≤ p.H ^ 2 := one_le_pow₀ hH
    have hmul := one_le_mul_of_one_le_of_one_le hm hpow
    linarith
  · unfold radius
    field_simp

lemma certificate_noise_scale (p : Params) (hp : spec.valid p) :
    sensitivity p * (certificateError p ^ 2 + ridge p ^ 2) ≤ radius p ^ 2 / 16 := by
  have hm : (p.m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.1).ne'
  have hH : p.H ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.2.1).ne'
  have hid : sensitivity p * (certificateError p ^ 2 + ridge p ^ 2) =
      (1025 / 65536 : ℝ) * radius p ^ 2 := by
    unfold sensitivity certificateError ridge radius
    field_simp [hm, hH]
    ring
  rw [hid]
  nlinarith [sq_nonneg (radius p)]

lemma certificate_conditions (p : Params) (hp : spec.valid p) :
    p.H * certificateError p ≤ 1 / 2 ∧ radius p / (2 * eta p) ≤ 1 ∧
    radius p / (2 * eta p) + certificateError p * (1 + rho p / 2) ≤ p.ε ∧
    certificateError p + p.H * (radius p / 2) + ridge p * (rho p / 2) ≤ p.ε ∧
    ridge p * (rho p / 2) ^ 2 + (rho p / 2) *
      (certificateError p + p.H * (radius p / 2)) ≤ p.ε := by
  obtain ⟨hρ, hγ, he, hτ, hid⟩ := basic_scale_bounds p hp
  have hpos := valid_tuning_positive p hp
  have hsc := variance_scales_positive p hp
  have hH := hp.2.1
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast (Nat.succ_le_iff.mpr hp.1)
  have hH0 : 0 ≤ p.H := le_trans zero_le_one hH
  have hH2 : p.H ≤ p.H ^ 2 := by nlinarith
  have hH3 : p.H ^ 2 ≤ p.H ^ 3 := by nlinarith [mul_nonneg (sq_nonneg p.H) (sub_nonneg.mpr hH)]
  have hH4 : p.H ^ 2 ≤ p.H ^ 4 := by nlinarith [sq_nonneg (p.H ^ 2 - 1)]
  have hMH : p.H ^ 3 ≤ p.m * p.H ^ 3 := by
    exact le_mul_of_one_le_left (by positivity) hm
  let B := (p.m : ℝ) * p.H ^ 3 * radius p
  have hB : 64 * B = p.ε := by dsimp [B]; nlinarith [hid]
  have hrB : radius p ≤ B := by
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ (p.m : ℝ) * p.H ^ 3 by linarith) hsc.2.1.le
    simpa only [one_mul, B] using h
  have hHrB : p.H * radius p ≤ B := by
    exact mul_le_mul_of_nonneg_right (by linarith) hsc.2.1.le
  have hH2rB : p.H ^ 2 * radius p ≤ B :=
    mul_le_mul_of_nonneg_right (by linarith) hsc.2.1.le
  have hH3rB : p.H ^ 3 * radius p ≤ B :=
    mul_le_mul_of_nonneg_right hMH hsc.2.1.le
  have hη : radius p / (2 * eta p) = 2 * gamma p * radius p := by
    unfold eta
    field_simp [hpos.2.1.ne']
    ring
  have hηB : radius p / (2 * eta p) ≤ 20 * B := by
    rw [hη]
    have h := mul_le_mul_of_nonneg_right hγ hsc.2.1.le
    dsimp [B]
    nlinarith
  have hHe := mul_le_mul_of_nonneg_left he hH0
  have hρr := mul_le_mul_of_nonneg_right hρ hsc.2.1.le
  have hstatE : certificateError p * (1 + rho p / 2) ≤ 5 * B := by
    have h := mul_le_mul_of_nonneg_right he (show 0 ≤ 1 + rho p / 2 by have := hpos.1; positivity)
    nlinarith
  have hτsmall : ridge p * (rho p / 2) ≤ radius p := by
    have h := mul_le_mul_of_nonneg_left hρ hpos.2.2.2.le
    have hh := mul_le_mul_of_nonneg_right hH4 hpos.2.2.2.le
    nlinarith [hpos.2.2.2.le]
  have hτsq : ridge p * (rho p / 2) ^ 2 ≤ radius p := by
    have hρsq := (sq_le_sq₀ hpos.1.le (show 0 ≤ 8 * p.H ^ 2 by positivity)).mpr hρ
    have h := mul_le_mul_of_nonneg_left hρsq hpos.2.2.2.le
    nlinarith
  have hprod : (rho p / 2) * (certificateError p + p.H * (radius p / 2)) ≤ 6 * B := by
    have hh := mul_le_mul (show rho p / 2 ≤ 4 * p.H ^ 2 by linarith)
      (add_le_add he le_rfl)
      (show 0 ≤ certificateError p + p.H * (radius p / 2) by
        have := hsc.2.2.1; have := hsc.2.1; positivity)
      (show 0 ≤ 4 * p.H ^ 2 by positivity)
    nlinarith
  have hε := hp.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end LongTails.Proofs.SurjectiveProxLinearCertificateTuning
