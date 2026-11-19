import LongTails.Algorithms.FullRangeTuned
import LongTails.Proofs.SmoothBanachTuning

namespace LongTails.Proofs.FullRangeTuning

open LongTails.Algorithms.FullRangeTuned
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params)

variable (q : Params) (hL : 0 < q.L) (hρ : 0 ≤ q.ρ) (hρL : q.ρ * q.L < 1) (hR : 0 ≤ q.R)
  (hσ : 0 ≤ q.σ) (hε : 0 < q.ε)

include hρL in
lemma tau_pos : 0 < tau q := by unfold tau; linarith

include hρ hL in
lemma tau_le_one : tau q ≤ 1 := by unfold tau; nlinarith [mul_nonneg hρ hL.le]

include hL hρ in
lemma eta_pos : 0 < eta q := by unfold eta; have := one_div_pos.mpr hL; linarith

include hL in
lemma etaL_eq : eta q * q.L = (q.ρ * q.L + 1) / 2 := by
  unfold eta
  field_simp

include hL hρL in
lemma etaL_lt : eta q * q.L < 1 := by rw [etaL_eq q hL]; linarith

include hL in
lemma mu_eq : 1 - eta q * q.L = tau q / 2 := by rw [etaL_eq q hL]; unfold tau; ring

include hL hρL in
lemma tau_eta_le : tau q * eta q ≤ 2 * (eta q - q.ρ) := by
  have h1 : eta q - q.ρ = tau q / (2 * q.L) := by
    unfold eta tau
    field_simp
    ring
  have h2 : eta q ≤ 1 / q.L := by
    have := etaL_lt q hL hρL
    rw [le_div_iff₀ hL]
    linarith
  rw [h1]
  have ht : 0 < tau q := tau_pos q hρL
  have : tau q * eta q ≤ tau q * (1 / q.L) := mul_le_mul_of_nonneg_left h2 ht.le
  calc tau q * eta q ≤ tau q * (1 / q.L) := this
    _ = 2 * (tau q / (2 * q.L)) := by field_simp

include hL hρ hρL in
lemma gamma0_step : gamma0 q * (1 + eta q * q.L) ^ 2 ≤ 1 - eta q * q.L := by
  rw [mu_eq q hL]
  have h1 : eta q * q.L < 1 := etaL_lt q hL hρL
  have h0 : 0 ≤ eta q * q.L := (mul_pos (eta_pos q hL hρ) hL).le
  have hsq : (1 + eta q * q.L) ^ 2 ≤ 4 := by nlinarith
  have ht : 0 < tau q := tau_pos q hρL
  unfold gamma0
  nlinarith

include hL hρ hρL hε in
lemma epsT_pos : 0 < epsT q := by
  unfold epsT
  have := tau_pos q hρL
  have := eta_pos q hL hρ
  positivity

include hL hρ hρL hε hR in
lemma radius_pos : 0 < radius q := by
  unfold radius
  have := epsT_pos q hL hρ hρL hε
  linarith

include hL hρ hρL hε in
lemma radius_half : q.R ≤ radius q / 2 := by
  unfold radius
  have := epsT_pos q hL hρ hρL hε
  linarith

lemma batch_pos : 0 < batch q := by unfold batch; omega

lemma n0_pos : 0 < n0 q := by unfold n0; omega

include hL in
lemma gamma0_mu : gamma0 q * (1 - eta q * q.L) = tau q ^ 2 / 16 := by
  rw [mu_eq q hL]
  unfold gamma0
  ring

include hL hρ hρL hε hR in
lemma theta_pos : 0 < theta q := by
  have hr := radius_pos q hL hρ hρL hR hε
  have he := epsT_pos q hL hρ hρL hε
  have ht := tau_pos q hρL
  have hLL := hL
  have hS : (0 : ℝ) < (stages q : ℝ) := by unfold stages; exact_mod_cast Nat.succ_pos _
  unfold theta
  refine lt_min (by positivity) (lt_min (by positivity) (by positivity))

include hL hρ hρL hε hR in
lemma kappa0_le : Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) ≤ theta q := by
  rw [gamma0_mu q hL]
  have hθ := theta_pos q hL hρ hρL hR hε
  have ht := tau_pos q hρL
  have hn : 16 / tau q ^ 2 * (Real.log (1 / theta q) + 8) ≤ n0 q := by
    unfold n0
    push_cast
    have := Nat.le_ceil (16 / tau q ^ 2 * (Real.log (1 / theta q) + 8))
    linarith
  have hge : Real.log (1 / theta q) ≤ tau q ^ 2 / 16 * n0 q := by
    have := mul_le_mul_of_nonneg_left hn (show 0 ≤ tau q ^ 2 / 16 by positivity)
    have e : tau q ^ 2 / 16 * (16 / tau q ^ 2 * (Real.log (1 / theta q) + 8)) =
        Real.log (1 / theta q) + 8 := by field_simp
    linarith
  have hlog : Real.exp (-(tau q ^ 2 / 16 * n0 q)) ≤ Real.exp (-Real.log (1 / theta q)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.log_div (by norm_num) hθ.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hθ] at hlog
  exact hlog

include hL hρ hρL hε hR in
lemma theta_le_one : theta q ≤ 1 := by
  have he := epsT_pos q hL hρ hρL hε
  have hr : 2 * epsT q ≤ radius q := by unfold radius; linarith
  have hS : (1 : ℝ) ≤ (stages q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ stages q := by unfold stages; exact_mod_cast Nat.succ_pos _
    nlinarith
  have h1 : theta q ≤ epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2 * (9 * radius q ^ 2)) := min_le_left _ _
  refine h1.trans ?_
  rw [div_le_one (by have := radius_pos q hL hρ hρL hR hε; positivity)]
  have hr2 : 4 * epsT q ^ 2 ≤ radius q ^ 2 := by nlinarith
  nlinarith [sq_nonneg (epsT q)]

include hL hρ hρL hε hR in
lemma kappa_le : Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q / 2)) ≤ 1 / 16 := by
  rw [gamma0_mu q hL]
  have hθ := theta_pos q hL hρ hρL hR hε
  have ht := tau_pos q hρL
  have hθ1 := theta_le_one q hL hρ hρL hR hε
  have hl0 : 0 ≤ Real.log (1 / theta q) := Real.log_nonneg (by rw [le_div_iff₀ hθ]; linarith)
  have hn : 16 / tau q ^ 2 * (Real.log (1 / theta q) + 8) ≤ n0 q := by
    unfold n0
    push_cast
    have := Nat.le_ceil (16 / tau q ^ 2 * (Real.log (1 / theta q) + 8))
    linarith
  have hge : 4 ≤ tau q ^ 2 / 16 * n0 q / 2 := by
    have := mul_le_mul_of_nonneg_left hn (show 0 ≤ tau q ^ 2 / 16 by positivity)
    have e : tau q ^ 2 / 16 * (16 / tau q ^ 2 * (Real.log (1 / theta q) + 8)) =
        Real.log (1 / theta q) + 8 := by field_simp
    linarith
  have h1 : Real.exp (-(tau q ^ 2 / 16 * n0 q / 2)) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-4) ≤ 1 / 16 := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have he := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
    have : Real.exp 4 = Real.exp 2 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith [he]
  have e : -(tau q ^ 2 / 16 * ↑(n0 q) / 2) = -(tau q ^ 2 / 16 * ↑(n0 q) / 2) := rfl
  linarith

include hL hρL in
lemma drift_eq : gamma0 q * (eta q ^ 2 * q.σ ^ 2) / (1 - eta q * q.L) = driftConst q := by
  rw [mu_eq q hL]
  have ht := tau_pos q hρL
  unfold gamma0 driftConst
  field_simp
  ring

lemma stages_pos : (0 : ℝ) < stages q := by unfold stages; exact_mod_cast Nat.succ_pos _

lemma two_pow_top : 104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 ≤ (2 : ℝ) ^ top q := by
  unfold top
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2)
    ⌈104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1⌉₊
  have h2 := Nat.le_ceil (104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1)
  have h3 : ((⌈104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤
      ((2 ^ Nat.clog 2 ⌈104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3
  linarith

include hL hρ hρL hε hR in
lemma variance_tolerance :
    (2 : ℝ) ^ (top q + 5) * (Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * (9 * radius q ^ 2)) +
      tau q ^ 2 * ((24 * top q + 4) * (gamma0 q * (eta q ^ 2 * q.σ ^ 2) / (1 - eta q * q.L))) ≤
      sigmaT q ^ 2 := by
  rw [drift_eq q hL hρL]
  have hd : 0 ≤ driftConst q := by unfold driftConst; positivity
  unfold sigmaT
  rw [Real.sq_sqrt (by positivity)]
  have hk := kappa0_le q hL hρ hρL hR hε
  have hθ : theta q ≤ epsT q ^ 2 / ((2 : ℝ) ^ (top q + 5) * (9 * radius q ^ 2)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hr := radius_pos q hL hρ hρL hR hε
  have hpos : 0 < (2 : ℝ) ^ (top q + 5) * (9 * radius q ^ 2) := by positivity
  have h1 : Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * ((2 : ℝ) ^ (top q + 5) *
      (9 * radius q ^ 2)) ≤ epsT q ^ 2 := by
    have := mul_le_mul_of_nonneg_right (hk.trans hθ) hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  nlinarith

include hL hρ hρL hε hR in
lemma bias_tolerance :
    Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * (9 * radius q ^ 2) +
      tau q ^ 2 * (2 * (gamma0 q * (eta q ^ 2 * q.σ ^ 2) / (1 - eta q * q.L)) / (2 : ℝ) ^ top q) ≤
      (epsT q / (80 * (stages q : ℝ))) ^ 2 := by
  rw [drift_eq q hL hρL]
  have hk := kappa0_le q hL hρ hρL hR hε
  have hθ : theta q ≤ epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2 * (9 * radius q ^ 2)) := min_le_left _ _
  have hr := radius_pos q hL hρ hρL hR hε
  have hS := stages_pos q
  have hpos : 0 < 12800 * (stages q : ℝ) ^ 2 * (9 * radius q ^ 2) := by positivity
  have h1 : Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * (9 * radius q ^ 2) ≤
      epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2) := by
    have := mul_le_mul_of_nonneg_right (hk.trans hθ) (show 0 ≤ 9 * radius q ^ 2 by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  have htop := two_pow_top q
  have h2p : (0 : ℝ) < (2 : ℝ) ^ top q := by positivity
  have he : epsT q = tau q * eta q * q.ε / 128 := rfl
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have h2 : tau q ^ 2 * (2 * driftConst q / (2 : ℝ) ^ top q) ≤ epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2) := by
    have hX : 104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 ≤ (2 : ℝ) ^ top q * q.ε ^ 2 :=
      (div_le_iff₀ (by positivity)).mp htop
    have e1 : tau q ^ 2 * (2 * driftConst q / (2 : ℝ) ^ top q) =
        (tau q ^ 2 * eta q ^ 2 * q.σ ^ 2) / (2 * (2 : ℝ) ^ top q) := by
      unfold driftConst
      field_simp
      ring
    have e2 : epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2) =
        (tau q ^ 2 * eta q ^ 2 * q.ε ^ 2) / (209715200 * (stages q : ℝ) ^ 2) := by
      rw [he]
      field_simp
      ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hA : 0 ≤ tau q ^ 2 * eta q ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hX hA]
  have e : (epsT q / (80 * (stages q : ℝ))) ^ 2 = epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2) +
      epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e]
  linarith

include hL hρ hρL hε hR in
lemma cert_path_tolerance {D : ℝ} (hD : tau q * D ≤ 3 * radius q) (hD0 : 0 ≤ D) :
    3 * q.L * Real.sqrt (Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * D ^ 2 +
      2 * (gamma0 q * (eta q ^ 2 * q.σ ^ 2) / (1 - eta q * q.L)) / (2 : ℝ) ^ top q) ≤ q.ε / 8 := by
  rw [drift_eq q hL hρL]
  have hk := kappa0_le q hL hρ hρL hR hε
  have ht := tau_pos q hρL
  have hr := radius_pos q hL hρ hρL hR hε
  have hθ : theta q ≤ tau q ^ 2 * q.ε ^ 2 / (1152 * q.L ^ 2 * (9 * radius q ^ 2)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hD2 : tau q ^ 2 * D ^ 2 ≤ 9 * radius q ^ 2 := by nlinarith [mul_nonneg ht.le hD0]
  have h1 : Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * D ^ 2 ≤ q.ε ^ 2 / (1152 * q.L ^ 2) := by
    have hk2 := hk.trans hθ
    have hA := mul_le_mul_of_nonneg_right hk2 (sq_nonneg D)
    refine hA.trans ?_
    have e : tau q ^ 2 * q.ε ^ 2 / (1152 * q.L ^ 2 * (9 * radius q ^ 2)) * D ^ 2 =
        q.ε ^ 2 / (1152 * q.L ^ 2) * ((tau q ^ 2 * D ^ 2) / (9 * radius q ^ 2)) := by
      field_simp
    rw [e]
    have hf : (tau q ^ 2 * D ^ 2) / (9 * radius q ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hD2
    have hc : 0 ≤ q.ε ^ 2 / (1152 * q.L ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hf hc]
  have htop := two_pow_top q
  have hη := eta_pos q hL hρ
  have hηL : eta q * q.L ≤ 1 := (etaL_lt q hL hρL).le
  have h2 : 2 * driftConst q / (2 : ℝ) ^ top q ≤ q.ε ^ 2 / (1152 * q.L ^ 2) := by
    have hX : 104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 ≤ (2 : ℝ) ^ top q * q.ε ^ 2 :=
      (div_le_iff₀ (by positivity)).mp htop
    have hS1 : (1 : ℝ) ≤ (stages q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ stages q := by unfold stages; exact_mod_cast Nat.succ_pos _
      nlinarith
    have hX2 : 576 * q.σ ^ 2 ≤ (2 : ℝ) ^ top q * q.ε ^ 2 := by nlinarith [sq_nonneg q.σ]
    unfold driftConst
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hηL2 : (eta q * q.L) ^ 2 ≤ 1 := by nlinarith [mul_pos hη hL]
    nlinarith [mul_le_mul_of_nonneg_left hηL2 (sq_nonneg q.σ), sq_nonneg q.σ]
  have hsum : Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * D ^ 2 + 2 * driftConst q / (2 : ℝ) ^ top q
      ≤ (q.ε / (24 * q.L)) ^ 2 := by
    have : (q.ε / (24 * q.L)) ^ 2 = q.ε ^ 2 / (1152 * q.L ^ 2) + q.ε ^ 2 / (1152 * q.L ^ 2) := by
      field_simp
      ring
    linarith
  have hs := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_sq (by positivity)] at hs
  have := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 * q.L by positivity)
  calc _ ≤ 3 * q.L * (q.ε / (24 * q.L)) := this
    _ = q.ε / 8 := by field_simp; ring

include hσ hε in
lemma batch_tolerance : 3 * (q.σ / Real.sqrt (batch q)) ≤ q.ε / 8 := by
  have hB : (576 * q.σ ^ 2 / q.ε ^ 2) ≤ batch q := by
    unfold batch
    push_cast
    have := Nat.le_ceil (576 * q.σ ^ 2 / q.ε ^ 2)
    linarith
  have hBp : (0 : ℝ) < batch q := by exact_mod_cast batch_pos q
  have hs : 24 * q.σ / q.ε ≤ Real.sqrt (batch q) := by
    rw [show 24 * q.σ / q.ε = Real.sqrt ((24 * q.σ / q.ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have : (24 * q.σ / q.ε) ^ 2 = 576 * q.σ ^ 2 / q.ε ^ 2 := by field_simp; ring
    linarith
  have hsp : 0 < Real.sqrt (batch q) := Real.sqrt_pos.mpr hBp
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < q.ε)] at hs
  rw [mul_div_assoc', div_le_iff₀ hsp]
  nlinarith

include hL hρ hρL hε in
lemma cert_scale : 4 * epsT q / (tau q * eta q) = q.ε / 32 := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  unfold epsT
  field_simp
  ring

include hL hρ hρL hε hR in
lemma failure_pos : 0 < failureProb q := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have hr := radius_pos q hL hρ hρL hR hε
  unfold failureProb
  positivity

include hL hρ hρL hε hR in
lemma failure_tolerance :
    failureProb q * (q.ε / 8 + q.ε / 8 + 3 * radius q / (tau q * eta q)) ≤ q.ε / 8 := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have hr := radius_pos q hL hρ hρL hR hε
  unfold failureProb
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hx : q.ε / 8 + q.ε / 8 + 3 * radius q / (tau q * eta q) =
      (q.ε * tau q * eta q / 4 + 3 * radius q) / (tau q * eta q) := by
    field_simp
    ring
  rw [hx]
  have hte : 0 < tau q * eta q := by positivity
  rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hte]
  nlinarith [mul_pos (mul_pos hε ht) hη, mul_pos hε hr]

include hL hρ hρL hε hR in
lemma failure_le_one : failureProb q ≤ 1 := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have hr := radius_pos q hL hρ hρL hR hε
  unfold failureProb
  rw [div_le_one (by positivity)]
  nlinarith [mul_pos (mul_pos hε ht) hη]

end LongTails.Proofs.FullRangeTuning
