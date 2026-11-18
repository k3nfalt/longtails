import LongTails.Proofs.DistributedJacobianStrongGrowthParameters
import LongTails.Algorithms.DistributedLocalExtragradientTuning

namespace LongTails.Proofs.DistributedJacobianStrongGrowthBudgetAlgebra

lemma radius_normalized {L μ R ρ B M : ℝ} (hL : 0 < L) :
    L * R / (L + 32 * (L / μ) * ρ * B * M * R) =
      R / (1 + 32 * ρ * M * R * B / μ) := by
  have he : L + 32 * (L / μ) * ρ * B * M * R =
      L * (1 + 32 * ρ * M * R * B / μ) := by ring
  rw [he, mul_div_mul_left _ _ hL.ne']

lemma refinement_log (r ε : ℝ) :
    Real.log (4 * r ^ 2 / ε ^ 2) = 2 * Real.log (2 * r / ε) := by
  have he : 4 * r ^ 2 / ε ^ 2 = (2 * r / ε) ^ 2 := by ring
  rw [he, Real.log_pow]
  norm_num

lemma refinement_count_normalized (κ T r ε : ℝ) :
    ⌈(2 / (T / (64 * κ))) * Real.log (4 * r ^ 2 / ε ^ 2)⌉₊ =
      ⌈256 * ((κ / T) * Real.log (2 * r / ε))⌉₊ := by
  rw [refinement_log r ε]
  congr 1
  simp only [div_div_eq_mul_div]
  ring

lemma ceil_scaled (a : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ⌈a⌉₊ ≤ ⌈(m : ℝ) * a⌉₊ ∧ ⌈(m : ℝ) * a⌉₊ ≤ m * ⌈a⌉₊ := by
  constructor
  · by_cases ha : a ≤ 0
    · rw [Nat.ceil_eq_zero.mpr ha]
      exact Nat.zero_le _
    · apply Nat.ceil_mono
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
  · apply Nat.ceil_le.mpr
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil a) (Nat.cast_nonneg m)

lemma refinement_count_comparison (κ T r ε : ℝ) :
    ⌈(κ / T) * Real.log (2 * r / ε)⌉₊ ≤
      ⌈(2 / (T / (64 * κ))) * Real.log (4 * r ^ 2 / ε ^ 2)⌉₊ ∧
    ⌈(2 / (T / (64 * κ))) * Real.log (4 * r ^ 2 / ε ^ 2)⌉₊ ≤
      256 * ⌈(κ / T) * Real.log (2 * r / ε)⌉₊ := by
  rw [refinement_count_normalized κ T r ε]
  exact ceil_scaled _ 256 (by norm_num)

lemma warm_computation_envelope {κ ρ n A J : ℝ}
    (hκ : 1 ≤ κ) (hρ : 1 ≤ ρ) (hn : 8 * ρ * κ ≤ n)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) :
    (⌈ρ * κ ^ 2 * (6 + 2 * A + (2 / n) * (3 + 2 * J))⌉₊ : ℝ) ≤
      10 * ρ * κ ^ 2 * (1 + A) + κ * J / 2 := by
  have hk : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hratio : ρ * κ ^ 2 / n ≤ κ / 8 := by
    apply (div_le_iff₀ hnpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hn hk.le]
  have hscale : 1 ≤ ρ * κ ^ 2 := by nlinarith [sq_nonneg (κ - 1)]
  have hsmall : κ ≤ ρ * κ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hρ (sq_nonneg κ)]
  have hx : 0 ≤ ρ * κ ^ 2 * (6 + 2 * A + (2 / n) * (3 + 2 * J)) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  have he : ρ * κ ^ 2 * (6 + 2 * A + (2 / n) * (3 + 2 * J)) =
      ρ * κ ^ 2 * (6 + 2 * A) + (ρ * κ ^ 2 / n) * (6 + 4 * J) := by ring
  rw [he] at hc ⊢
  have hh := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 6 + 4 * J)
  have ha := mul_nonneg (by positivity : 0 ≤ ρ * κ ^ 2) hA
  nlinarith

lemma refinement_computation_envelope {κ T z J : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) (hTk : T ≤ κ) (hJ : 0 ≤ J) (hz : z ≤ 1 + J) :
    2 * T * (⌈256 * (κ / T) * z⌉₊ : ℝ) ≤ 514 * κ * (1 + J) := by
  have hm := Nat.ceil_mono (mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 256 * (κ / T)))
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 256 * (κ / T) * (1 + J))
  have hnm : (⌈256 * (κ / T) * z⌉₊ : ℝ) ≤ (⌈256 * (κ / T) * (1 + J)⌉₊ : ℝ) := by exact_mod_cast hm
  have hn : (⌈256 * (κ / T) * z⌉₊ : ℝ) < 256 * (κ / T) * (1 + J) + 1 :=
    hnm.trans_lt hc
  have hh := mul_lt_mul_of_pos_left hn (by positivity : 0 < 2 * T)
  have he : 2 * T * (256 * (κ / T) * (1 + J) + 1) = 512 * κ * (1 + J) + 2 * T := by
    field_simp
    ring
  rw [he] at hh
  nlinarith

lemma computation_reverse_envelope {κ ρ T A J z s : ℝ}
    (hκ : 1 ≤ κ) (hρ : 1 ≤ ρ) (hT : 0 < T) (hA : 0 ≤ A)
    (hJ : J ≤ A + max z 0) (hs : ρ * κ ^ 2 * A ≤ s) :
    κ * J ≤ s + T * (⌈256 * (κ / T) * z⌉₊ : ℝ) := by
  have hk : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hsmall : κ ≤ ρ * κ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hρ (sq_nonneg κ)]
  have ha := (mul_le_mul_of_nonneg_right hsmall hA).trans hs
  have hj := mul_le_mul_of_nonneg_left hJ hk.le
  have hcount := mul_le_mul_of_nonneg_left (Nat.le_ceil (256 * (κ / T) * z)) hT.le
  have he : T * (256 * (κ / T) * z) = 256 * κ * z := by field_simp
  rw [he] at hcount
  have hn : 0 ≤ T * (⌈256 * (κ / T) * z⌉₊ : ℝ) := by positivity
  by_cases hz : 0 ≤ z
  · rw [max_eq_left hz] at hj
    nlinarith [mul_nonneg hk.le hz]
  · rw [max_eq_right (le_of_not_ge hz)] at hj
    linarith

lemma initialization_log_bound {d q : ℝ} (hd : 1 ≤ d) (hq : 1 ≤ q) :
    Real.log (64 * d * q ^ 2) ≤ 6 + 2 * Real.log (d * q) := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    have he : (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [Real.log_mul (mul_ne_zero (by norm_num) hdpos.ne') (pow_ne_zero _ hqpos.ne'),
    Real.log_mul (by norm_num) hdpos.ne', Real.log_pow, h64,
    Real.log_mul hdpos.ne' hqpos.ne']
  norm_num only [Nat.cast_ofNat]
  nlinarith [Real.log_nonneg hd]

lemma confidence_log_bound {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    Real.log (8 * R ^ 2 / ε ^ 2) ≤ 3 + 2 * Real.log (R / ε) := by
  have he : 8 * R ^ 2 / ε ^ 2 = 8 * (R / ε) ^ 2 := by ring
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    have hh : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [hh, Real.log_pow]
    norm_num
  rw [he, Real.log_mul (by norm_num) (pow_ne_zero _ (div_pos hR hε).ne'),
    Real.log_pow, h8]
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  norm_num only [Nat.cast_ofNat]
  linarith

lemma radius_ratio_log {R r ε : ℝ} (hR : 0 < R) (hr : 0 < r) (hε : 0 < ε) :
    Real.log (R / ε) ≤ Real.log (R / r) + max (Real.log (2 * r / ε)) 0 := by
  have he : R / ε = (R / r) * (r / ε) := by field_simp
  have hz : Real.log (r / ε) ≤ Real.log (2 * r / ε) := by
    apply Real.log_le_log (div_pos hr hε)
    apply div_le_div_of_nonneg_right _ hε.le
    linarith
  rw [he, Real.log_mul (div_pos hR hr).ne' (div_pos hr hε).ne']
  exact add_le_add le_rfl (hz.trans (le_max_left _ _))

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthParameters

lemma rich_workers_computation (p : Params) (hp : valid p)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    8 * p.ρ * (p.L / p.μ) ≤ (p.n : ℝ) := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have hg : p.ρ / 8 ≤ growth p := by dsimp [growth]; nlinarith [sq_nonneg p.ρ]
  nlinarith [mul_le_mul_of_nonneg_left hg hk.le]

lemma warmCount_computation_envelope (p : Params) (hp : valid p) (T : ℕ)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) (hε : p.ε < p.R) :
    (warmCount p T : ℝ) ≤
      10 * p.ρ * (p.L / p.μ) ^ 2 * (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) +
        (p.L / p.μ) * Real.log (p.R / p.ε) / 2 := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 1 ≤ p.L / p.μ := (one_le_div hμ).mpr hp.2.2.2.2.2.2.2.1
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have hεpos : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := radius_properties p hp T
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hq : 1 ≤ p.R / radius p T := (one_le_div hr.1).mpr hr.2.1
  have hA : 0 ≤ Real.log ((p.d : ℝ) * (p.R / radius p T)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
  have hJ : 0 ≤ Real.log (p.R / p.ε) := Real.log_nonneg ((one_le_div hεpos).mpr hε.le)
  have hinit := initialization_log_bound hd hq
  have he : (64 : ℝ) * p.d * p.R ^ 2 / radius p T ^ 2 =
      64 * p.d * (p.R / radius p T) ^ 2 := by ring
  rw [← he] at hinit
  have hconfidence := confidence_log_bound (hεpos.trans hε) hεpos
  have hb := warm_computation_envelope hk hρ (rich_workers_computation p hp hn) hA hJ
  apply le_trans ?_ hb
  apply Nat.cast_le.mpr
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ p.ρ * (p.L / p.μ) ^ 2)
  exact add_le_add hinit (mul_le_mul_of_nonneg_left hconfidence (by positivity))

lemma refinement_log_bound {R r ε : ℝ} (hr : 0 < r) (hR : r ≤ R) (hε : 0 < ε) :
    Real.log (2 * r / ε) ≤ 1 + Real.log (R / ε) := by
  have he : 2 * r / ε = 2 * (r / ε) := by ring
  rw [he, Real.log_mul (by norm_num) (div_pos hr hε).ne']
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact add_le_add htwo (Real.log_le_log (div_pos hr hε) (div_le_div_of_nonneg_right hR hε.le))

lemma refinementCount_computation_envelope (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hTk : (T : ℝ) ≤ p.L / p.μ) (hε : p.ε < p.R) :
    2 * (T : ℝ) * (refinementCount p T : ℝ) ≤
      514 * (p.L / p.μ) * (1 + Real.log (p.R / p.ε)) := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 0 < p.L / p.μ := div_pos (hμ.trans_le hp.2.2.2.2.2.2.2.1) hμ
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := radius_properties p hp T
  have hJ : 0 ≤ Real.log (p.R / p.ε) := Real.log_nonneg ((one_le_div he).mpr hε.le)
  have hcount : refinementCount p T = ⌈256 * (((p.L / p.μ) / (T : ℝ)) * Real.log (2 * radius p T / p.ε))⌉₊ :=
    refinement_count_normalized (p.L / p.μ) (T : ℝ) (radius p T) p.ε
  rw [hcount]
  simpa only [mul_assoc] using refinement_computation_envelope hk ht hTk hJ (refinement_log_bound hr.1 hr.2.1 he)

lemma initialization_log_lower {d q : ℝ} (hd : 0 < d) (hq : 1 ≤ q) :
    1 + Real.log (d * q) ≤ Real.log (64 * d * q ^ 2) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    have he : (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [Real.log_mul hd.ne' hqpos.ne',
    Real.log_mul (mul_ne_zero (by norm_num) hd.ne') (pow_ne_zero _ hqpos.ne'),
    Real.log_mul (by norm_num) hd.ne', Real.log_pow, h64]
  norm_num only [Nat.cast_ofNat]
  linarith [Real.log_nonneg hq]

lemma warmCount_startup_lower (p : Params) (hp : valid p) (T : ℕ) (hε : p.ε < p.R) :
    p.ρ * (p.L / p.μ) ^ 2 * (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) ≤
      (warmCount p T : ℝ) := by
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := radius_properties p hp T
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hq : 1 ≤ p.R / radius p T := (one_le_div hr.1).mpr hr.2.1
  have hi := initialization_log_lower hd hq
  have heq : (64 : ℝ) * p.d * p.R ^ 2 / radius p T ^ 2 =
      64 * p.d * (p.R / radius p T) ^ 2 := by ring
  rw [← heq] at hi
  have hconf : 0 ≤ Real.log (8 * p.R ^ 2 / p.ε ^ 2) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    nlinarith
  apply le_trans ?_ (Nat.le_ceil _)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ p.ρ * (p.L / p.μ) ^ 2)
  exact hi.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hconf))

lemma computation_count_upper (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hTk : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) (hε : p.ε < p.R) :
    ((warmCount p T + 2 * T * refinementCount p T : ℕ) : ℝ) ≤
      1024 * (p.L / p.μ) * (p.ρ * (p.L / p.μ) *
        (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) + Real.log (p.R / p.ε)) := by
  have hw := warmCount_computation_envelope p hp T hn hε
  have href := refinementCount_computation_envelope p hp T hT hTk hε
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 1 ≤ p.L / p.μ := (one_le_div hμ).mpr hp.2.2.2.2.2.2.2.1
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := radius_properties p hp T
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hq : 1 ≤ p.R / radius p T := (one_le_div hr.1).mpr hr.2.1
  have hA : 0 ≤ Real.log ((p.d : ℝ) * (p.R / radius p T)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
  have hJ : 0 ≤ Real.log (p.R / p.ε) := Real.log_nonneg ((one_le_div he).mpr hε.le)
  have hsmall : p.L / p.μ ≤ p.ρ * (p.L / p.μ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hρ (sq_nonneg (p.L / p.μ))]
  have hinit : p.L / p.μ ≤ p.ρ * (p.L / p.μ) ^ 2 *
      (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ p.ρ * (p.L / p.μ) ^ 2) hA]
  have haccuracy : 0 ≤ (p.L / p.μ) * Real.log (p.R / p.ε) := mul_nonneg (by linarith) hJ
  push_cast
  nlinarith

lemma computation_count_lower (p : Params) (hp : valid p) (T : ℕ)
    (hT : 1 ≤ T) (hε : p.ε < p.R) :
    (p.L / p.μ) * (p.ρ * (p.L / p.μ) *
      (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) + Real.log (p.R / p.ε)) ≤
        2 * ((warmCount p T + 2 * T * refinementCount p T : ℕ) : ℝ) := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hk : 1 ≤ p.L / p.μ := (one_le_div hμ).mpr hp.2.2.2.2.2.2.2.1
  have hρ : 1 ≤ p.ρ := hp.2.2.2.2.2.2.2.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hr := radius_properties p hp T
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hq : 1 ≤ p.R / radius p T := (one_le_div hr.1).mpr hr.2.1
  have hA : 0 ≤ 1 + Real.log ((p.d : ℝ) * (p.R / radius p T)) := by
    have hh := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd hq)
    linarith
  have hJ : Real.log (p.R / p.ε) ≤
      (1 + Real.log ((p.d : ℝ) * (p.R / radius p T))) + max (Real.log (2 * radius p T / p.ε)) 0 := by
    have hh := radius_ratio_log (he.trans hε) hr.1 he
    rw [Real.log_mul (by positivity : (p.d : ℝ) ≠ 0) (div_pos (he.trans hε) hr.1).ne']
    linarith [Real.log_nonneg hd]
  have hs := warmCount_startup_lower p hp T hε
  have hrev := computation_reverse_envelope hk hρ ht hA hJ hs
  have hc : refinementCount p T =
      ⌈256 * ((p.L / p.μ) / (T : ℝ)) * Real.log (2 * radius p T / p.ε)⌉₊ := by
    simpa only [refinementCount, contraction, mul_assoc] using
      refinement_count_normalized (p.L / p.μ) (T : ℝ) (radius p T) p.ε
  rw [← hc] at hrev
  have hn : 0 ≤ (T : ℝ) * (refinementCount p T : ℝ) := by positivity
  push_cast
  nlinarith

lemma worker_depth_maximal {κ G n : ℝ} (hκ : 1 ≤ κ) (hG : 1 < G)
    (hn : 64 * κ * G ≤ n) (T : ℕ) (hT : (T : ℝ) ≤ κ) (hworkers : 64 * κ * G ^ T ≤ n) :
    T ≤ min ⌊κ⌋₊ ⌊Real.log (n / (64 * κ)) / Real.log G⌋₊ := by
  have hk : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hg : 0 < G := lt_trans zero_lt_one hG
  have hnp : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hp : G ^ T ≤ n / (64 * κ) := by
    apply (le_div_iff₀ (by positivity : 0 < 64 * κ)).mpr
    nlinarith
  have hl := Real.log_le_log (pow_pos hg T) hp
  rw [Real.log_pow] at hl
  have hquot : (T : ℝ) ≤ Real.log (n / (64 * κ)) / Real.log G :=
    (le_div_iff₀ (Real.log_pos hG)).mpr hl
  exact Nat.le_min.mpr ⟨Nat.le_floor hT, Nat.le_floor hquot⟩

lemma worker_depth_next_infeasible {κ G n : ℝ} (hκ : 1 ≤ κ) (hG : 1 < G)
    (hn : 64 * κ * G ≤ n) :
    let T := min ⌊κ⌋₊ ⌊Real.log (n / (64 * κ)) / Real.log G⌋₊
    κ < (T + 1 : ℕ) ∨ n < 64 * κ * G ^ (T + 1) := by
  intro T
  by_contra h
  push Not at h
  have hh := worker_depth_maximal hκ hG hn (T + 1) h.1 h.2
  change T + 1 ≤ T at hh
  omega

lemma worker_depth_unique {κ G n : ℝ} (hκ : 1 ≤ κ) (hG : 1 < G)
    (hn : 64 * κ * G ≤ n) (T : ℕ) (hT : (T : ℝ) ≤ κ) (hworkers : 64 * κ * G ^ T ≤ n)
    (hnext : κ < (T + 1 : ℕ) ∨ n < 64 * κ * G ^ (T + 1)) :
    T = min ⌊κ⌋₊ ⌊Real.log (n / (64 * κ)) / Real.log G⌋₊ := by
  apply Nat.le_antisymm (worker_depth_maximal hκ hG hn T hT hworkers)
  by_contra h
  have ht : T + 1 ≤ min ⌊κ⌋₊ ⌊Real.log (n / (64 * κ)) / Real.log G⌋₊ := by omega
  have hh := DistributedJacobianStrongGrowthTuning.worker_local_depth hκ hG hn
  rcases hnext with hnext | hnext
  · have hc : ((T + 1 : ℕ) : ℝ) ≤ _ := Nat.cast_le.mpr ht
    exact hnext.not_ge (hc.trans hh.2.1)
  · have hp := pow_le_pow_right₀ hG.le ht
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 64 * κ)
    exact hnext.not_ge (hm.trans hh.2.2)

lemma radius_ratio_explicit (p : Params) (hp : valid p) (T : ℕ) :
    p.R / radius p T = 1 + 32 * p.ρ * p.M * p.R * growth p ^ T / p.μ := by
  have hμ : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hL : 0 < p.L := hμ.trans_le hp.2.2.2.2.2.2.2.1
  have hR : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  simp only [radius, div_div_eq_mul_div]
  field_simp

end LongTails.Proofs.DistributedJacobianStrongGrowthBudgetAlgebra
