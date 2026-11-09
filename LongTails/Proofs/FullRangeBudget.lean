import LongTails.Proofs.FullRangeTuning
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.FullRangeBudget

open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeTuned
open LongTails.Proofs.FullRangeTuning
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params)

lemma clog_real (n : ℕ) (N : ℝ) (hn : 1 ≤ n) (hN : (n : ℝ) ≤ N) :
    (2 : ℝ) ^ Nat.clog 2 n ≤ 2 * N ∧ (Nat.clog 2 n : ℝ) ≤ 1 + 2 * Real.log N := by
  have hN1 : (1 : ℝ) ≤ N := le_trans (by exact_mod_cast hn) hN
  have hpow : (2 : ℝ) ^ Nat.clog 2 n ≤ 2 * N := by
    rcases Nat.lt_or_ge 1 n with h | h
    · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
      have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h
      have h2 : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
        rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hc).symm
      have h3 : (2 : ℝ) ^ Nat.clog 2 n = 2 * (2 : ℝ) ^ (Nat.clog 2 n).pred := by exact_mod_cast h2
      have h4 : ((2 ^ (Nat.clog 2 n).pred : ℕ) : ℝ) < n := by exact_mod_cast h1
      push_cast at h4
      rw [h3]; linarith
    · have : n = 1 := le_antisymm h hn
      subst this
      simp only [Nat.clog_one_right, pow_zero]
      linarith
  refine ⟨hpow, ?_⟩
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at hl
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have : (Nat.clog 2 n : ℝ) * Real.log 2 ≤ (1 + 2 * Real.log N) * Real.log 2 := by nlinarith
  exact le_of_mul_le_mul_right this (by linarith)

lemma log_two_pow_le (m : ℕ) : Real.log ((2 : ℝ) ^ m) ≤ m := by
  rw [Real.log_pow]
  have := Real.log_two_lt_d9
  have hm : (0 : ℝ) ≤ m := by positivity
  nlinarith

variable (q : Params) (hL : 0 < q.L) (hρ : 0 ≤ q.ρ) (hρL : q.ρ * q.L < 1) (hR : 0 ≤ q.R)
  (hε : 0 < q.ε)

noncomputable def B : ℝ := 1 + q.L * q.R / (tau q * q.ε) + q.σ ^ 2 / q.ε ^ 2

noncomputable def Lam : ℝ :=
  1 + Real.log (2 + q.L * q.R / q.ε + q.σ ^ 2 / q.ε ^ 2) + Real.log (2 / tau q)

include hρ hL in
lemma tau_le_one : tau q ≤ 1 := by unfold tau; nlinarith

include hL hρL hR hε in
lemma B_ge_one : 1 ≤ B q := by
  have ht := tau_pos q hρL
  unfold B; have : 0 ≤ q.L * q.R / (tau q * q.ε) := by positivity
  have : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  linarith

include hL hρ hρL hR hε in
lemma log_B_le : Real.log (B q) ≤ Lam q - 1 := by
  have ht := tau_pos q hρL
  have ht1 := tau_le_one q hL hρ
  have ha : 0 ≤ q.L * q.R / q.ε := by positivity
  have hs : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hB : B q ≤ (2 + q.L * q.R / q.ε + q.σ ^ 2 / q.ε ^ 2) * (2 / tau q) := by
    unfold B
    have e : q.L * q.R / (tau q * q.ε) = q.L * q.R / q.ε / tau q := by field_simp
    rw [e]
    have h1 : q.L * q.R / q.ε / tau q ≤ q.L * q.R / q.ε * (2 / tau q) := by
      rw [div_eq_mul_one_div _ (tau q)]
      gcongr; norm_num
    have h2 : 1 ≤ 2 / tau q := by rw [le_div_iff₀ ht]; linarith
    nlinarith
  have := Real.log_le_log (by linarith [B_ge_one q hL hρL hR hε]) hB
  rw [Real.log_mul (by positivity) (by positivity)] at this
  unfold Lam; linarith

include hL hρ hρL hR hε in
lemma Lam_ge_one : 1 ≤ Lam q := by
  have := log_B_le q hL hρ hρL hR hε
  have := Real.log_nonneg (B_ge_one q hL hρL hR hε)
  linarith

include hL hρ hρL hR hε in
lemma log_B_le_Lam : Real.log (B q) ≤ Lam q := by
  linarith [log_B_le q hL hρ hρL hR hε]

include hL hρ hρL hR hε in
lemma log_Lam_le : Real.log (Lam q) ≤ Lam q := by
  have := Real.log_le_sub_one_of_pos (by linarith [Lam_ge_one q hL hρ hρL hR hε] : 0 < Lam q)
  linarith

lemma ceil_le_add (x : ℝ) (hx : 0 ≤ x) : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le

include hL hρ hρL hR hε in
lemma R_div_epsT : q.R / epsT q ≤ 256 * (q.L * q.R / (tau q * q.ε)) := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have h2 : 1 ≤ 2 * q.L * eta q := by
    unfold eta; field_simp; nlinarith
  unfold epsT
  rw [div_le_iff₀ (by positivity)]
  have e : 256 * (q.L * q.R / (tau q * q.ε)) * (tau q * eta q * q.ε / 128) = q.R * (2 * q.L * eta q) := by
    field_simp; ring
  rw [e]
  nlinarith

include hL hρ hρL hR hε in
lemma levels_bound : (2 : ℝ) ^ anchorLevels q ≤ 8192 * B q ∧ (stages q : ℝ) ≤ 28 * Lam q := by
  have he := epsT_pos q hL hρ hρL hε
  have hRe := R_div_epsT q hL hρ hρL hR hε
  have hB := B_ge_one q hL hρL hR hε
  have hx : 0 ≤ 16 * q.R / epsT q := by positivity
  have hN : ((⌈16 * q.R / epsT q⌉₊ + 1 : ℕ) : ℝ) ≤ 4096 * B q := by
    push_cast
    have := ceil_le_add _ hx
    have e : 16 * q.R / epsT q = 16 * (q.R / epsT q) := by ring
    have hb : q.L * q.R / (tau q * q.ε) = B q - 1 - q.σ ^ 2 / q.ε ^ 2 := by unfold B; ring
    have hs : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
    rw [e] at this ⊢
    nlinarith
  obtain ⟨h1, h2⟩ := clog_real _ _ (by omega) hN
  refine ⟨by unfold anchorLevels; linarith, ?_⟩
  have hl : Real.log (4096 * B q) ≤ 12 + Lam q := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := log_two_pow_le 12
    have := log_B_le_Lam q hL hρ hρL hR hε
    norm_num at *
    linarith
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  unfold stages
  push_cast
  unfold anchorLevels
  linarith

include hL hρ hρL hR hε in
lemma top_bound : (2 : ℝ) ^ top q ≤ 2 ^ 38 * Lam q ^ 2 * B q ∧ (top q : ℝ) ≤ 81 * Lam q := by
  obtain ⟨-, hS⟩ := levels_bound q hL hρ hρL hR hε
  have hB := B_ge_one q hL hρL hR hε
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  have hs0 : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hsB : q.σ ^ 2 / q.ε ^ 2 ≤ B q := by
    unfold B; have : 0 ≤ q.L * q.R / (tau q * q.ε) := by
      have := tau_pos q hρL; positivity
    linarith
  have hS0 : (0 : ℝ) ≤ stages q := by positivity
  have hS2 : (stages q : ℝ) ^ 2 ≤ 784 * Lam q ^ 2 := by nlinarith
  have hy : 0 ≤ 104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1 := by positivity
  have hN : ((⌈104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤
      2 ^ 37 * Lam q ^ 2 * B q := by
    have := ceil_le_add _ hy
    have e : 104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 =
        104857600 * (stages q : ℝ) ^ 2 * (q.σ ^ 2 / q.ε ^ 2) := by ring
    rw [e] at this ⊢
    have h1 : (stages q : ℝ) ^ 2 * (q.σ ^ 2 / q.ε ^ 2) ≤ 784 * Lam q ^ 2 * B q :=
      mul_le_mul hS2 hsB hs0 (by positivity)
    have h2 : 1 ≤ Lam q ^ 2 * B q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hΛ) hB
    nlinarith
  have hn1 : 1 ≤ ⌈104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  obtain ⟨h1, h2⟩ := clog_real _ _ hn1 hN
  refine ⟨by unfold top; linarith, ?_⟩
  have hl : Real.log (2 ^ 37 * Lam q ^ 2 * B q) ≤ 37 + 3 * Lam q := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow (Lam q) 2]
    have h37 : Real.log ((2 : ℝ) ^ 37) ≤ 37 := by exact_mod_cast log_two_pow_le 37
    have := log_B_le_Lam q hL hρ hρL hR hε
    have := log_Lam_le q hL hρ hρL hR hε
    push_cast
    linarith
  have h3 : 1 + 2 * Real.log (2 ^ 37 * Lam q ^ 2 * B q) ≤ 81 * Lam q := by linarith
  exact le_trans h2 h3

include hL hρ hρL hε in
lemma sigma_ratio : sigmaT q ^ 2 / epsT q ^ 2 = 1 + 4096 * (24 * top q + 4) * (q.σ ^ 2 / q.ε ^ 2) := by
  have he := epsT_pos q hL hρ hρL hε
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  unfold sigmaT
  rw [Real.sq_sqrt (by unfold driftConst; positivity)]
  unfold driftConst
  rw [add_div, div_self (by positivity)]
  congr 1
  unfold epsT
  field_simp
  ring

include hL hρ hρL hR hε in
lemma calls_bound : (calls q : ℝ) ≤ 2 ^ 56 * Lam q ^ 5 * B q := by
  obtain ⟨hl2, hS⟩ := levels_bound q hL hρ hρL hR hε
  obtain ⟨-, htop⟩ := top_bound q hL hρ hρL hR hε
  have hB := B_ge_one q hL hρL hR hε
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  have he := epsT_pos q hL hρ hρL hε
  have hs0 : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hsB : q.σ ^ 2 / q.ε ^ 2 ≤ B q := by
    unfold B; have : 0 ≤ q.L * q.R / (tau q * q.ε) := by
      have := tau_pos q hρL; positivity
    linarith
  have hS0 : (0 : ℝ) ≤ stages q := by positivity
  have hLev : (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) : ℝ) + 1 = stages q := by
    unfold stages anchorLevels; push_cast; rfl
  have hratio := sigma_ratio q hL hρ hρL hε
  have hr1 : sigmaT q ^ 2 / epsT q ^ 2 ≤ 2 ^ 23 * Lam q * B q := by
    rw [hratio]
    have h1 : (24 * (top q : ℝ) + 4) ≤ 1948 * Lam q := by linarith
    have h2 : (24 * (top q : ℝ) + 4) * (q.σ ^ 2 / q.ε ^ 2) ≤ 1948 * Lam q * B q :=
      mul_le_mul h1 hsB hs0 (by positivity)
    have h3 : 1 ≤ Lam q * B q := one_le_mul_of_one_le_of_one_le hΛ hB
    nlinarith
  obtain ⟨D, hD⟩ : ∃ D, D = 1 + (2 : ℝ) ^ LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) +
    1024 * (anchorParams q).C * (anchorParams q).σ ^ 2 *
      (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) + 1 : ℝ) ^ 2 /
        (anchorParams q).ε ^ 2 := ⟨_, rfl⟩
  have hDb : D ≤ 2 ^ 43 * Lam q ^ 3 * B q := by
    rw [hD]
    change 1 + (2 : ℝ) ^ anchorLevels q + 1024 * 1 * sigmaT q ^ 2 *
      (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) + 1 : ℝ) ^ 2 / epsT q ^ 2 ≤ _
    rw [hLev]
    have e : 1024 * 1 * sigmaT q ^ 2 * (stages q : ℝ) ^ 2 / epsT q ^ 2 =
        1024 * (sigmaT q ^ 2 / epsT q ^ 2) * (stages q : ℝ) ^ 2 := by ring
    rw [e]
    have hS2 : (stages q : ℝ) ^ 2 ≤ 784 * Lam q ^ 2 := by nlinarith
    have h4 : (sigmaT q ^ 2 / epsT q ^ 2) * (stages q : ℝ) ^ 2 ≤ (2 ^ 23 * Lam q * B q) * (784 * Lam q ^ 2) :=
      mul_le_mul hr1 hS2 (by positivity) (by positivity)
    have h5 : B q ≤ Lam q ^ 3 * B q := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hΛ)
    nlinarith
  have hrel : 8 * (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) + 1 : ℝ) /
      LongTails.Algorithms.SmoothBanachAnchoring.relaxation (anchorParams q) = 8 * stages q * D := by
    unfold LongTails.Algorithms.SmoothBanachAnchoring.relaxation
    rw [← hD, one_div, div_inv_eq_mul, hLev]
  have hin : (LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q) : ℝ) ≤
      2 ^ 51 * Lam q ^ 4 * B q := by
    unfold LongTails.Algorithms.SmoothBanachAnchoring.innerSteps
    have hD0 : 0 ≤ D := by rw [hD]; change 0 ≤ 1 + _ + 1024 * 1 * sigmaT q ^ 2 * _ / epsT q ^ 2; positivity
    have := ceil_le_add (8 * ((LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) : ℝ) + 1) /
      LongTails.Algorithms.SmoothBanachAnchoring.relaxation (anchorParams q)) (by rw [hrel]; positivity)
    rw [hrel] at this ⊢
    have h6 : (stages q : ℝ) * D ≤ (28 * Lam q) * (2 ^ 43 * Lam q ^ 3 * B q) :=
      mul_le_mul hS hDb hD0 (by positivity)
    have h7 : 1 ≤ Lam q ^ 4 * B q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hΛ) hB
    nlinarith
  unfold calls
  push_cast
  have h8 : (stages q : ℝ) * (LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q) : ℝ) ≤
      (28 * Lam q) * (2 ^ 51 * Lam q ^ 4 * B q) := mul_le_mul hS hin (by positivity) (by positivity)
  nlinarith

include hL hρ hρL hR hε in
lemma radius_ratio : radius q ≤ 512 * B q * epsT q := by
  have he := epsT_pos q hL hρ hρL hε
  have hRe := R_div_epsT q hL hρ hρL hR hε
  have hB := B_ge_one q hL hρL hR hε
  have hb : q.L * q.R / (tau q * q.ε) ≤ B q - 1 := by
    unfold B; have : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
    linarith
  have h1 : q.R ≤ 256 * (B q - 1) * epsT q := by
    rw [div_le_iff₀ he] at hRe; nlinarith
  unfold radius; nlinarith

include hL hρ hρL hR hε in
lemma radius_ratio' : q.L * radius q ≤ 2 * B q * (tau q * q.ε) := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have hηL := etaL_lt q hL hρL
  have hB := B_ge_one q hL hρL hR hε
  have hb : q.L * q.R / (tau q * q.ε) ≤ B q - 1 := by
    unfold B; have : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
    linarith
  have h1 : q.L * q.R ≤ (B q - 1) * (tau q * q.ε) := by
    rw [div_le_iff₀ (by positivity)] at hb; linarith
  have h2 : q.L * epsT q ≤ tau q * q.ε / 128 := by
    unfold epsT
    have : q.L * (tau q * eta q * q.ε / 128) = (eta q * q.L) * (tau q * q.ε) / 128 := by ring
    rw [this]
    have : 0 < tau q * q.ε := by positivity
    nlinarith
  unfold radius
  nlinarith [mul_pos ht hε]

include hL hρ hρL hR hε in
lemma log_theta_le : Real.log (1 / theta q) ≤ 70 * Lam q := by
  obtain ⟨-, hS⟩ := levels_bound q hL hρ hρL hR hε
  obtain ⟨htop, -⟩ := top_bound q hL hρ hρL hR hε
  have hB := B_ge_one q hL hρL hR hε
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  have he := epsT_pos q hL hρ hρL hε
  have ht := tau_pos q hρL
  have hr := radius_pos q hL hρ hρL hR hε
  have hrr := radius_ratio q hL hρ hρL hR hε
  have hrr' := radius_ratio' q hL hρ hρL hR hε
  set M : ℝ := 2 ^ 65 * Lam q ^ 2 * B q ^ 3 with hM
  have hM0 : 0 < M := by positivity
  have hS0 : (0 : ℝ) ≤ stages q := by positivity
  have hr2 : radius q ^ 2 ≤ 2 ^ 18 * B q ^ 2 * epsT q ^ 2 := by nlinarith
  have hB2 : B q ^ 2 ≤ B q ^ 3 := by nlinarith
  have hΛ2 : 1 ≤ Lam q ^ 2 := one_le_pow₀ hΛ
  have hθ : 1 / M ≤ theta q := by
    unfold theta
    refine le_min ?_ (le_min ?_ ?_)
    · have hSp := stages_pos q
      rw [div_le_div_iff₀ hM0 (by positivity), one_mul]
      have hS2 : (stages q : ℝ) ^ 2 ≤ 784 * Lam q ^ 2 := by nlinarith
      have h1 : (stages q : ℝ) ^ 2 * radius q ^ 2 ≤ (784 * Lam q ^ 2) * (2 ^ 18 * B q ^ 2 * epsT q ^ 2) :=
        mul_le_mul hS2 hr2 (by positivity) (by positivity)
      have h2 : Lam q ^ 2 * B q ^ 2 * epsT q ^ 2 ≤ Lam q ^ 2 * B q ^ 3 * epsT q ^ 2 := by gcongr
      rw [hM]; nlinarith
    · rw [div_le_div_iff₀ hM0 (by positivity), one_mul, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ]
      have h1 : (2 : ℝ) ^ top q * radius q ^ 2 ≤ (2 ^ 38 * Lam q ^ 2 * B q) * (2 ^ 18 * B q ^ 2 * epsT q ^ 2) :=
        mul_le_mul htop hr2 (by positivity) (by positivity)
      have e : B q * B q ^ 2 = B q ^ 3 := by ring
      rw [hM]; nlinarith
    · rw [div_le_div_iff₀ hM0 (by positivity), one_mul]
      have h1 : (q.L * radius q) ^ 2 ≤ (2 * B q * (tau q * q.ε)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hrr' 2
      have h3 : B q ^ 2 * (tau q * q.ε) ^ 2 ≤ Lam q ^ 2 * B q ^ 3 * (tau q * q.ε) ^ 2 := by
        have : B q ^ 2 ≤ Lam q ^ 2 * B q ^ 3 := by nlinarith
        gcongr
      rw [hM]; nlinarith
  have hθ0 : 0 < theta q := lt_of_lt_of_le (by positivity) hθ
  have hl : Real.log (1 / theta q) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hθ0]
    rw [div_le_iff₀ hM0] at hθ
    linarith
  have hlM : Real.log M ≤ 65 + 5 * Lam q := by
    rw [hM, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow (Lam q) 2, Real.log_pow (B q) 3]
    have h65 : Real.log ((2 : ℝ) ^ 65) ≤ 65 := by exact_mod_cast log_two_pow_le 65
    have := log_B_le_Lam q hL hρ hρL hR hε
    have := log_Lam_le q hL hρ hρL hR hε
    push_cast
    linarith
  linarith

include hL hρ hρL hR hε in
lemma n0_bound : (n0 q : ℝ) ≤ 2 ^ 11 * Lam q / tau q ^ 2 := by
  have ht := tau_pos q hρL
  have ht1 := tau_le_one q hL hρ
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  have hl := log_theta_le q hL hρ hρL hR hε
  have hθ0 := theta_pos q hL hρ hρL hR hε
  have hlog0 : 0 ≤ Real.log (1 / theta q) := Real.log_nonneg (by
    rw [le_div_iff₀ hθ0]; linarith [theta_le_one q hL hρ hρL hR hε])
  have hx : 0 ≤ 16 / tau q ^ 2 * (Real.log (1 / theta q) + 8) := by positivity
  have hc := ceil_le_add _ hx
  have ht2 : 0 < tau q ^ 2 := by positivity
  have ht21 : tau q ^ 2 ≤ 1 := by nlinarith
  unfold n0
  push_cast
  rw [le_div_iff₀ ht2]
  have e : 16 / tau q ^ 2 * (Real.log (1 / theta q) + 8) * tau q ^ 2 = 16 * (Real.log (1 / theta q) + 8) := by
    field_simp
  have h2 : ((⌈16 / tau q ^ 2 * (Real.log (1 / theta q) + 8)⌉₊ : ℝ) + 1) * tau q ^ 2 ≤
      (16 / tau q ^ 2 * (Real.log (1 / theta q) + 8) + 2) * tau q ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) ht2.le
  have e2 : (16 / tau q ^ 2 * (Real.log (1 / theta q) + 8) + 2) * tau q ^ 2 =
      16 * (Real.log (1 / theta q) + 8) + 2 * tau q ^ 2 := by field_simp
  rw [e2] at h2
  nlinarith

include hL hρ hρL hR hε in
lemma failure_log : (⌈Real.log (1 / failureProb q)⌉₊ : ℝ) + 1 ≤ 10 * Lam q := by
  have ht := tau_pos q hρL
  have hη := eta_pos q hL hρ
  have he := epsT_pos q hL hρ hρL hε
  have hr := radius_pos q hL hρ hρL hR hε
  have hB := B_ge_one q hL hρL hR hε
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  have hrr := radius_ratio q hL hρ hρL hR hε
  have hd := failure_pos q hL hρ hρL hR hε
  have hd1 := failure_le_one q hL hρ hρL hR hε
  have hinv : 1 / failureProb q ≤ 2 ^ 7 * B q := by
    unfold failureProb
    rw [one_div_div]
    have e : q.ε * tau q * eta q = 128 * epsT q := by unfold epsT; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hl : Real.log (1 / failureProb q) ≤ 7 + Lam q := by
    have := Real.log_le_log (by positivity) hinv
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    have h7 := Real.log_two_lt_d9
    have := log_B_le_Lam q hL hρ hρL hR hε
    linarith
  have h0 : 0 ≤ Real.log (1 / failureProb q) := Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)
  have := ceil_le_add _ h0
  linarith

include hL hρ hρL hR hε in
theorem totalCalls_le : (totalCalls q : ℝ) ≤ 2 ^ 79 * B q / tau q ^ 2 * Lam q ^ 7 := by
  have ht := tau_pos q hρL
  have ht1 := tau_le_one q hL hρ
  have hB := B_ge_one q hL hρL hR hε
  have hΛ := Lam_ge_one q hL hρ hρL hR hε
  obtain ⟨htop2, htop⟩ := top_bound q hL hρ hρL hR hε
  have hc := calls_bound q hL hρ hρL hR hε
  have hn := n0_bound q hL hρ hρL hR hε
  have hf := failure_log q hL hρ hρL hR hε
  have ht2 : 0 < tau q ^ 2 := by positivity
  have ht21 : tau q ^ 2 ≤ 1 := by nlinarith
  set T := tau q ^ 2 with hT
  set Λ := Lam q with hΛdef
  set b := B q with hb
  have hn' : (n0 q : ℝ) * T ≤ 2 ^ 11 * Λ := by rwa [le_div_iff₀ ht2] at hn
  have hbatch : (batch q : ℝ) ≤ 2 ^ 10 * b := by
    unfold batch
    have hs0 : 0 ≤ 576 * q.σ ^ 2 / q.ε ^ 2 := by positivity
    have := ceil_le_add _ hs0
    have hsB : q.σ ^ 2 / q.ε ^ 2 ≤ b - 1 := by
      rw [hb]; unfold B; have : 0 ≤ q.L * q.R / (tau q * q.ε) := by positivity
      linarith
    have e : 576 * q.σ ^ 2 / q.ε ^ 2 = 576 * (q.σ ^ 2 / q.ε ^ 2) := by ring
    push_cast
    rw [e] at this ⊢
    nlinarith
  have hn0 : (0 : ℝ) ≤ n0 q := by positivity
  have hcall0 : (0 : ℝ) ≤ calls q := by positivity
  have hΛ1 : ∀ k : ℕ, 1 ≤ Λ ^ k := fun k => one_le_pow₀ hΛ
  -- inner bracket of seedLimit
  have hin : 2 * (calls q : ℝ) * ((top q : ℝ) + 1) + 2 ^ top q * ((⌈Real.log (1 / failureProb q)⌉₊ : ℝ) + 1) ≤
      2 ^ 66 * Λ ^ 6 * b := by
    have h1 : (calls q : ℝ) * ((top q : ℝ) + 1) ≤ (2 ^ 56 * Λ ^ 5 * b) * (82 * Λ) :=
      mul_le_mul hc (by linarith) (by positivity) (by positivity)
    have h2 : (2 : ℝ) ^ top q * ((⌈Real.log (1 / failureProb q)⌉₊ : ℝ) + 1) ≤ (2 ^ 38 * Λ ^ 2 * b) * (10 * Λ) :=
      mul_le_mul htop2 hf (by positivity) (by positivity)
    have h3 : Λ ^ 3 * b ≤ Λ ^ 6 * b :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hΛ (by norm_num)) (by linarith)
    have e1 : (2 ^ 56 * Λ ^ 5 * b) * (82 * Λ) = 82 * 2 ^ 56 * (Λ ^ 6 * b) := by ring
    have e2 : (2 ^ 38 * Λ ^ 2 * b) * (10 * Λ) = 10 * 2 ^ 38 * (Λ ^ 3 * b) := by ring
    rw [e1] at h1; rw [e2] at h2
    nlinarith
  have hseed : (seedLimit q : ℝ) * T ≤ 2 ^ 78 * Λ ^ 7 * b := by
    unfold seedLimit
    push_cast
    have h0 : (0 : ℝ) ≤ 2 * (calls q : ℝ) * ((top q : ℝ) + 1) +
        2 ^ top q * ((⌈Real.log (1 / failureProb q)⌉₊ : ℝ) + 1) := by positivity
    have h1 : (n0 q : ℝ) * T * (2 * (calls q : ℝ) * ((top q : ℝ) + 1) +
        2 ^ top q * ((⌈Real.log (1 / failureProb q)⌉₊ : ℝ) + 1)) ≤ (2 ^ 11 * Λ) * (2 ^ 66 * Λ ^ 6 * b) :=
      mul_le_mul hn' hin h0 (by positivity)
    have e : (2 ^ 11 * Λ) * (2 ^ 66 * Λ ^ 6 * b) = 2 ^ 77 * (Λ ^ 7 * b) := by ring
    rw [e] at h1
    nlinarith
  have hlev : (levelTime (n0 q) (top q) : ℝ) * T ≤ 2 ^ 49 * Λ ^ 7 * b := by
    unfold levelTime
    push_cast
    have h1 : (n0 q : ℝ) * T * 2 ^ top q ≤ (2 ^ 11 * Λ) * (2 ^ 38 * Λ ^ 2 * b) :=
      mul_le_mul hn' htop2 (by positivity) (by positivity)
    have h3 : Λ ^ 3 * b ≤ Λ ^ 7 * b :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hΛ (by norm_num)) (by linarith)
    have e : (2 ^ 11 * Λ) * (2 ^ 38 * Λ ^ 2 * b) = 2 ^ 49 * (Λ ^ 3 * b) := by ring
    rw [e] at h1
    nlinarith
  have hrest : (2 * (batch q : ℝ) + 1) * T ≤ 2 ^ 12 * Λ ^ 7 * b := by
    have h7 : b ≤ Λ ^ 7 * b := le_mul_of_one_le_left (by linarith) (hΛ1 7)
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ ht2]
  unfold totalCalls
  push_cast
  nlinarith

end LongTails.Proofs.FullRangeBudget
