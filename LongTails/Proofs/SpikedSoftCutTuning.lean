import LongTails.Algorithms.SpikedSoftCutMethod
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.SpikedSoftCutTuning

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod

noncomputable def logScale (q : Params) : ℝ :=
  1+Real.log (16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε))

lemma logScale_ge_one (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    1 ≤ logScale q := by
  have hz : 0 ≤ q.G*q.R/q.ε := by positivity
  have hm : 1 ≤ (q.m+1 : ℝ) := by linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
  have hx : 1 ≤ 16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε) := by nlinarith
  have hl := Real.log_nonneg hx
  dsimp [logScale]
  linarith

lemma logScale_ge_three (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    3 ≤ logScale q := by
  have hz : 0 ≤ q.G*q.R/q.ε := by positivity
  have hm : 1 ≤ (q.m+1 : ℝ) := by linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
  have hx : 16 ≤ 16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε) := by nlinarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hx
  have he : Real.log (16 : ℝ) = 4*Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 4
    norm_num at hh ⊢
    exact hh
  rw [he] at hl
  dsimp [logScale]
  linarith [Real.log_two_gt_d9]

lemma tuned_inner_count_bounds (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    4096*(q.m+1 : ℝ)*(logScale q)^2 ≤ (tunedConfig q).T ∧
      ((tunedConfig q).T : ℝ) ≤ 4097*(q.m+1 : ℝ)*(logScale q)^2 := by
  have hQ := logScale_ge_one q hG hR hε
  have hd : 1 ≤ (q.m+1 : ℝ) := by linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
  have hbase : 1 ≤ (q.m+1 : ℝ)*(logScale q)^2 := by nlinarith [sq_nonneg (logScale q-1)]
  change 4096*(q.m+1 : ℝ)*(logScale q)^2 ≤ ⌈4096*(q.m+1 : ℝ)*(logScale q)^2⌉₊ ∧ _
  refine ⟨Nat.le_ceil _, ?_⟩
  have hu := Nat.ceil_lt_add_one (show 0 ≤ 4096*(q.m+1 : ℝ)*(logScale q)^2 by positivity)
  change (⌈4096*(q.m+1 : ℝ)*(logScale q)^2⌉₊ : ℝ) ≤ _
  linarith

lemma log_le_nat_of_le_two_pow (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : x ≤ (2 : ℝ)^n) :
    Real.log x ≤ n := by
  have hh := Real.log_le_log hx hn
  rw [Real.log_pow] at hh
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa using hh.trans hm

lemma logScale_component_bounds (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    Real.log (q.m+1 : ℝ) ≤ logScale q ∧
      Real.log (1+q.G*q.R/q.ε) ≤ logScale q := by
  have hz : 0 ≤ q.G*q.R/q.ε := by positivity
  have hd : 1 ≤ (q.m+1 : ℝ) := by linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
  have h₁ : (q.m+1 : ℝ) ≤ 16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε) := by nlinarith
  have h₂ : 1+q.G*q.R/q.ε ≤ 16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε) := by nlinarith
  have l₁ := Real.log_le_log (by positivity : 0 < (q.m+1 : ℝ)) h₁
  have l₂ := Real.log_le_log (by positivity : 0 < 1+q.G*q.R/q.ε) h₂
  dsimp [logScale]
  constructor <;> linarith

lemma batch_proxy_envelope (v R ε Q : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (hQ : 0 < Q) :
    v / (max 1 ⌈2^31*v*R^2*Q/ε^2⌉₊ : ℕ) ≤ ε^2/(2^31*R^2*Q) := by
  let b := max 1 ⌈2^31*v*R^2*Q/ε^2⌉₊
  have hb : 0 < (b : ℝ) := by
    have hh : 1 ≤ b := le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hc : 2^31*v*R^2*Q/ε^2 ≤ (b : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (show ⌈(2 : ℝ)^31*v*R^2*Q/ε^2⌉₊ ≤ b from le_max_right _ _))
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  change v/(b : ℝ) ≤ ε^2/(2^31*R^2*Q)
  apply (div_le_div_iff₀ hb (by positivity)).mpr
  nlinarith

lemma scalar_proxy_envelope (v r ε K : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (hK : 0 < K) :
    v / (max 1 ⌈8192*K*v*r^2/ε^2⌉₊ : ℕ) ≤ ε^2/(8192*K*r^2) := by
  let n := max 1 ⌈8192*K*v*r^2/ε^2⌉₊
  have hn : 0 < (n : ℝ) := by
    have hh : 1 ≤ n := le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hc : 8192*K*v*r^2/ε^2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (show ⌈(8192 : ℝ)*K*v*r^(2 : ℕ)/ε^2⌉₊ ≤ n from le_max_right _ _))
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  change v/(n : ℝ) ≤ ε^2/(8192*K*r^2)
  apply (div_le_div_iff₀ hn (by positivity)).mpr
  nlinarith

lemma tunedConfig_positive (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    0 < (tunedConfig q).α ∧ 0 < (tunedConfig q).T ∧ 0 < (tunedConfig q).b ∧
      0 < (tunedConfig q).n ∧ 0 < (tunedConfig q).K ∧ ∀ k, 0 < (tunedConfig q).N k := by
  have hQ : 0 < logScale q := lt_of_lt_of_le zero_lt_one (logScale_ge_one q hG hR hε)
  have hT : 0 < (tunedConfig q).T := by
    change 0 < ⌈4096*(q.m+1 : ℝ)*(logScale q)^2⌉₊
    apply Nat.ceil_pos.mpr
    positivity
  have hK : 0 < (tunedConfig q).K := by
    change 0 < ⌈32*logScale q⌉₊
    apply Nat.ceil_pos.mpr
    positivity
  refine ⟨?_, hT, ?_, ?_, hK, ?_⟩
  · change 0 < q.ε/8
    positivity
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  · change 0 < ⌈256*(1+8*q.R*q.G/q.ε+((tunedConfig q).T : ℝ))⌉₊
    apply Nat.ceil_pos.mpr
    positivity
  · intro k
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma tuned_inner_log_bound (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    Real.log ((tunedConfig q).T : ℝ) ≤ 7*logScale q := by
  have hQ := logScale_ge_three q hG hR hε
  have hQp : 0 < logScale q := by linarith
  have hT : 0 < ((tunedConfig q).T : ℝ) := by
    exact_mod_cast (tunedConfig_positive q hG hR hε).2.1
  have hh := Real.log_le_log hT (tuned_inner_count_bounds q hG hR hε).2
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
  have hc := log_le_nat_of_le_two_pow 4097 (by norm_num) 13 (by norm_num)
  have hd := (logScale_component_bounds q hG hR hε).1
  have hl := Real.log_le_sub_one_of_pos hQp
  norm_num at hc hh
  linarith

lemma tuned_epoch_count_bounds (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    32*logScale q ≤ (tunedConfig q).K ∧ ((tunedConfig q).K : ℝ) ≤ 33*logScale q := by
  have hQ := logScale_ge_one q hG hR hε
  change 32*logScale q ≤ ⌈32*logScale q⌉₊ ∧ (⌈32*logScale q⌉₊ : ℝ) ≤ _
  refine ⟨Nat.le_ceil _, ?_⟩
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 32*logScale q by positivity)
  linarith

lemma tuned_entropy_bound (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1) +
      ((tunedConfig q).T : ℝ)*Real.log (16*((tunedConfig q).T : ℝ)+1) +
      Real.log (400*((tunedConfig q).K : ℝ)) ≤
      43*((tunedConfig q).T : ℝ)*logScale q := by
  let T : ℝ := (tunedConfig q).T
  let K : ℝ := (tunedConfig q).K
  let Q := logScale q
  have hQ : 3 ≤ Q := logScale_ge_three q hG hR hε
  have hQp : 0 < Q := by linarith
  have hT1 : 1 ≤ T := by
    dsimp [T]
    exact_mod_cast Nat.succ_le_of_lt (tunedConfig_positive q hG hR hε).2.1
  have hKp : 0 < K := by
    dsimp [K]
    exact_mod_cast (tunedConfig_positive q hG hR hε).2.2.2.2.1
  have hTl : 4096*(q.m+1 : ℝ)*Q^2 ≤ T := (tuned_inner_count_bounds q hG hR hε).1
  have hm : (q.m : ℝ) ≤ T := by
    have hh : 1 ≤ Q^2 := by nlinarith
    have hx := mul_le_mul_of_nonneg_left hh (show 0 ≤ (q.m+1 : ℝ) by positivity)
    nlinarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
  have hlm : Real.log (16*(q.m : ℝ)+1) ≤ Q := by
    have hz : 0 ≤ q.G*q.R/q.ε := by positivity
    have hx : 16*(q.m : ℝ)+1 ≤ 16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε) := by
      nlinarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
    have hh := Real.log_le_log (by positivity : 0 < 16*(q.m : ℝ)+1) hx
    dsimp [Q, logScale]
    linarith
  have hlT : Real.log (16*T+1) ≤ 9*Q := by
    have hh := Real.log_le_log (by positivity : 0 < 16*T+1) (show 16*T+1 ≤ 17*T by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at hh
    have hc := log_le_nat_of_le_two_pow 17 (by norm_num) 5 (by norm_num)
    have ht : Real.log T ≤ 7*Q := tuned_inner_log_bound q hG hR hε
    norm_num at hc
    linarith
  have hlK : Real.log (400*K) ≤ 6*Q := by
    have hk : K ≤ 33*Q := (tuned_epoch_count_bounds q hG hR hε).2
    have hh := Real.log_le_log (by positivity : 0 < 400*K) (show 400*K ≤ 13200*Q by linarith)
    rw [Real.log_mul (by norm_num) hQp.ne'] at hh
    have hc := log_le_nat_of_le_two_pow 13200 (by norm_num) 14 (by norm_num)
    have hq := Real.log_le_sub_one_of_pos hQp
    norm_num at hc
    linarith
  have h₁ := mul_le_mul_of_nonneg_left hlm (Nat.cast_nonneg q.m : (0 : ℝ) ≤ q.m)
  have h₂ := mul_le_mul_of_nonneg_left hlT (show 0 ≤ T by linarith)
  have h₃ := mul_le_mul_of_nonneg_right hm hQp.le
  have h₄ := mul_le_mul_of_nonneg_right hT1 hQp.le
  change (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1)+T*Real.log (16*T+1)+Real.log (400*K) ≤ 43*T*Q
  nlinarith

lemma density_log_bound (R G α T Q z : ℝ) (hR : 0 < R) (hα : 0 < α)
    (hG : 0 ≤ G) (hT : 1 ≤ T) (hQ : 3 ≤ Q) (hz : 0 ≤ z)
    (hscale : R*G/α = 8*z) (hTl : Real.log T ≤ 7*Q)
    (hzl : Real.log (1+z) ≤ Q) :
    Real.log (R/(α/(192*(G+α*T/R)))) ≤ 20*Q := by
  have hTp : 0 < T := by linarith
  have hM : 0 < G+α*T/R := by positivity
  have he : R/(α/(192*(G+α*T/R))) = 192*(R*G/α+T) := by field_simp
  rw [he, hscale]
  have hx : 192*(8*z+T) ≤ 1536*(1+z)*T := by
    have hh := mul_nonneg hz (show 0 ≤ T-1 by linarith)
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 192*(8*z+T)) hx
  rw [Real.log_mul (show 1536*(1+z) ≠ 0 by positivity) hTp.ne',
    Real.log_mul (by norm_num : (1536 : ℝ) ≠ 0) (show 1+z ≠ 0 by positivity)] at hl
  have hc := log_le_nat_of_le_two_pow 1536 (by norm_num) 11 (by norm_num)
  norm_num at hc
  linarith

lemma density_iterations_tuning (m T Q L : ℝ) (hm : 0 ≤ m) (hQ : 3 ≤ Q)
    (hT : 4096*(m+1)*Q^2 ≤ T) (hL : L ≤ 20*Q) : 48*m*L ≤ T := by
  have hq : 0 ≤ Q := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hL (show 0 ≤ 48*m by positivity)
  have h₂ := mul_nonneg (show 0 ≤ m+1 by positivity) (show 0 ≤ Q*(Q-3) by positivity)
  have h₃ := mul_nonneg hm hq
  nlinarith

lemma max_ceil_bound (x : ℝ) (hx : 0 ≤ x) : (max 1 ⌈x⌉₊ : ℕ) ≤ x+1 := by
  rw [Nat.cast_max]
  apply max_le
  · norm_num
    linarith
  · exact (Nat.ceil_lt_add_one hx).le

lemma tuned_batch_count_bound (q : Params) (hG : 0 < q.G) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hv : 0 ≤ q.vRest) :
    ((tunedConfig q).b : ℝ) ≤ 1+2^31*q.vRest*q.R^2*logScale q/q.ε^2 := by
  have hQ := logScale_ge_one q hG hR hε
  have hh := max_ceil_bound (2^31*q.vRest*q.R^2*logScale q/q.ε^2) (by positivity)
  change ((max 1 ⌈2^31*q.vRest*q.R^2*logScale q/q.ε^2⌉₊ : ℕ) : ℝ) ≤ _
  linarith

lemma tuned_scalar_count_bound (q : Params) (hv : 0 ≤ q.vTop) (k : ℕ) :
    ((tunedConfig q).N k : ℝ) ≤ 1+8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2/q.ε^2 := by
  have hK : 0 ≤ ((tunedConfig q).K : ℝ) := Nat.cast_nonneg _
  have hh := max_ceil_bound (8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2*(5/8 : ℝ)^(2*k)/q.ε^2) (by positivity)
  have hp : (5/8 : ℝ)^(2*k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2/q.ε^2 by positivity)
  rw [div_mul_eq_mul_div, mul_one] at hm
  change ((max 1 ⌈8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2*(5/8 : ℝ)^(2*k)/q.ε^2⌉₊ : ℕ) : ℝ) ≤ _
  linarith

lemma contraction_power_bound (n : ℕ) (Q : ℝ) (hn : 8*Q ≤ 3*(n : ℝ)) :
    (5/8 : ℝ)^n ≤ Real.exp (-Q) := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5/8)
  have hh := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : (5/8 : ℝ)^n = Real.exp ((n : ℝ)*Real.log (5/8)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma tuned_last_radius (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    q.G*q.R*(5/8 : ℝ)^((tunedConfig q).K-1) ≤ q.ε/16 := by
  have hQ := logScale_ge_one q hG hR hε
  have hK := (tunedConfig_positive q hG hR hε).2.2.2.2.1
  have hKl := (tuned_epoch_count_bounds q hG hR hε).1
  have hncast : (((tunedConfig q).K-1 : ℕ) : ℝ) = ((tunedConfig q).K : ℝ)-1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hK), Nat.cast_one]
  have hn : 8*logScale q ≤ 3*(((tunedConfig q).K-1 : ℕ) : ℝ) := by
    rw [hncast]
    linarith
  have hp := contraction_power_bound ((tunedConfig q).K-1) (logScale q) hn
  let X := 16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε)
  have hX : 0 < X := by dsimp [X]; positivity
  have he : Real.exp (-logScale q) ≤ 1/X := by
    have hh : -logScale q ≤ -Real.log X := by dsimp [logScale,X]; linarith
    have hx := Real.exp_le_exp.mpr hh
    rw [Real.exp_neg (Real.log X), Real.exp_log hX] at hx
    simpa only [one_div] using hx
  have hb : 1/X ≤ q.ε/(16*q.G*q.R) := by
    apply (div_le_div_iff₀ hX (by positivity)).mpr
    have hd : 1 ≤ (q.m+1 : ℝ) := by linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
    have hz : 0 ≤ q.G*q.R/q.ε := by positivity
    have hprod : q.G*q.R ≤ q.ε*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε) := by
      have hdiv : q.ε*(q.G*q.R/q.ε) = q.G*q.R := by field_simp
      have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ q.ε*(1+q.G*q.R/q.ε) by positivity)
      nlinarith
    dsimp [X]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left (hp.trans (he.trans hb)) (show 0 ≤ q.G*q.R by positivity)
  have hc : q.G*q.R*(q.ε/(16*q.G*q.R)) = q.ε/16 := by field_simp
  exact hm.trans_eq hc

lemma tuned_scalar_variance (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) (k : ℕ) :
    q.vTop/((tunedConfig q).N k : ℝ) ≤
      q.ε^2/(8192*((tunedConfig q).K : ℝ)*(q.R*(5/8 : ℝ)^k)^2) := by
  have hr : 0 < q.R*(5/8 : ℝ)^k := by positivity
  have hK : 0 < ((tunedConfig q).K : ℝ) := by
    exact_mod_cast (tunedConfig_positive q hG hR hε).2.2.2.2.1
  have hh := scalar_proxy_envelope q.vTop (q.R*(5/8 : ℝ)^k) q.ε ((tunedConfig q).K : ℝ) hr hε hK
  have he : (q.R*(5/8 : ℝ)^k)^2 = q.R^2*(5/8 : ℝ)^(2*k) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
  rw [he] at hh ⊢
  have hn : max 1 ⌈8192*((tunedConfig q).K : ℝ)*q.vTop*(q.R^2*(5/8 : ℝ)^(2*k))/q.ε^2⌉₊ =
      (tunedConfig q).N k := by
    change max 1 ⌈8192*((tunedConfig q).K : ℝ)*q.vTop*(q.R^2*(5/8 : ℝ)^(2*k))/q.ε^2⌉₊ =
      max 1 ⌈8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2*(5/8 : ℝ)^(2*k)/q.ε^2⌉₊
    congr 2
    ring
  rw [hn] at hh
  exact hh

lemma grid_margin_tuning (α R G : ℝ) (hα : 0 < α) (hR : 0 < R) (hG : 0 ≤ G)
    (T n : ℕ) (hn : 0 < n) (hgrid : 256*(1+R*G/α+(T : ℝ)) ≤ n) :
    (α/2+2*R*(G+α*T/R))*T/n ≤ α*T/32 := by
  have hcancel : α*(256*(1+R*G/α+(T : ℝ))) = 256*α+256*R*G+256*α*T := by
    field_simp
  have hh := mul_le_mul_of_nonneg_left hgrid hα.le
  rw [hcancel] at hh
  have hRM : R*(G+α*T/R) = R*G+α*T := by field_simp
  have hc : (α/2+2*R*(G+α*T/R))/(n : ℝ) ≤ α/32 := by
    apply (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
    have hRG : 0 ≤ R*G := mul_nonneg hR.le hG
    have hαT : 0 ≤ α*(T : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg _)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  convert hm using 1 <;> ring

lemma scalar_exponential_failure (K : ℝ) (hK : 1 ≤ K) :
    2*Real.exp (-64*K) ≤ 1/(128*K) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp := Real.pow_div_factorial_le_exp (64*K) (show 0 ≤ 64*K by positivity) 2
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hp
  have hbound : 256*K ≤ Real.exp (64*K) := by nlinarith
  have hi := (inv_le_inv₀ (Real.exp_pos (64*K)) (show 0 < 256*K by positivity)).mpr hbound
  have hm := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
  have he : -64*K = -(64*K) := by ring
  rw [he, Real.exp_neg]
  exact hm.trans_eq (by ring)

lemma inner_noise_tuning (α ν R Q S T : ℝ) (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hproxy : 2^25*ν*R^2*Q ≤ α^2) (hentropy : S ≤ 43*T*Q) :
    R^2*(128*ν*S) ≤ α^2*T/4096 ∧
      2*(R^2*(128*ν*S)+128*ν*R^2*S)*T ≤ (α*T/32)^2 := by
  have h₁ := mul_le_mul_of_nonneg_left hentropy (show 0 ≤ 2^25*ν*R^2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hproxy (show 0 ≤ 43*T by positivity)
  have hαT : 0 ≤ α^2*T := mul_nonneg (sq_nonneg α) hT
  have hV : R^2*(128*ν*S) ≤ α^2*T/4096 := by nlinarith
  refine ⟨hV, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hV (show 0 ≤ 4*T by positivity)
  nlinarith

lemma error_cap_tuning (α R V T : ℝ) (hα : 0 ≤ α) (hR : 0 < R) (hV : 0 ≤ V)
    (hT : 1 ≤ T) (hbound : R^2*V ≤ α^2*T/4096) :
    Real.sqrt V ≤ α*T/R := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hsq := Real.sq_sqrt hV
  have hden : 0 ≤ α*T/R := by positivity
  have hnum : R^2*V ≤ α^2*T^2 := by
    have hmono := mul_nonneg (sq_nonneg α) (show 0 ≤ T*(T-1) by positivity)
    nlinarith
  have hscaled : V ≤ α^2*T^2/R^2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith)
  have he : α^2*T^2/R^2 = (α*T/R)^2 := by ring
  rw [he] at hscaled
  nlinarith [Real.sqrt_nonneg V]

lemma tuned_inner_parameters (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε) :
    let c := tunedConfig q
    let Q := logScale q
    let ν := q.ε^2/(2^31*q.R^2*Q)
    let S := (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1)+(c.T : ℝ)*Real.log (16*(c.T : ℝ)+1)+Real.log (400*(c.K : ℝ))
    let V := 128*ν*S
    let W := 128*ν*q.R^2*S
    let M := q.G+c.α*c.T/q.R
    let r := c.α/(192*M)
    0 ≤ V ∧ 0 ≤ W ∧ q.G+Real.sqrt V ≤ M ∧ 0 < r ∧ r ≤ q.R ∧
      (q.m : ℝ)*Real.log (q.R/r) ≤ (c.T : ℝ)/48 ∧ 2*r*M ≤ c.α/96 ∧
      (c.α/2+2*q.R*M)*c.T/c.n ≤ c.α*c.T/32 ∧
      2*(q.R^2*V+W)*c.T ≤ (c.α*c.T/32)^2 := by
  dsimp only
  let c := tunedConfig q
  let Q := logScale q
  let ν := q.ε^2/(2^31*q.R^2*Q)
  let S := (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1)+(c.T : ℝ)*Real.log (16*(c.T : ℝ)+1)+Real.log (400*(c.K : ℝ))
  let V := 128*ν*S
  let W := 128*ν*q.R^2*S
  let M := q.G+c.α*c.T/q.R
  let r := c.α/(192*M)
  have hc := tunedConfig_positive q hG hR hε
  have hα : 0 < c.α := hc.1
  have hT : 1 ≤ (c.T : ℝ) := by dsimp [c]; exact_mod_cast Nat.succ_le_of_lt hc.2.1
  have hK : 1 ≤ (c.K : ℝ) := by dsimp [c]; exact_mod_cast Nat.succ_le_of_lt hc.2.2.2.2.1
  have hQ : 3 ≤ Q := logScale_ge_three q hG hR hε
  have hQp : 0 < Q := by linarith
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hS : 0 ≤ S := by
    have hm := mul_nonneg (Nat.cast_nonneg q.m : (0 : ℝ) ≤ q.m)
      (Real.log_nonneg (show 1 ≤ 16*(q.m : ℝ)+1 by linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]))
    have ht := mul_nonneg (show 0 ≤ (c.T : ℝ) by positivity)
      (Real.log_nonneg (show 1 ≤ 16*(c.T : ℝ)+1 by linarith))
    have hk := Real.log_nonneg (show 1 ≤ 400*(c.K : ℝ) by linarith)
    dsimp [S]
    linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hproxy : 2^25*ν*q.R^2*Q ≤ c.α^2 := by
    have he : 2^25*ν*q.R^2*Q = c.α^2 := by
      change 2^25*(q.ε^2/(2^31*q.R^2*Q))*q.R^2*Q = (q.ε/8)^2
      field_simp
      ring
    exact he.le
  have hentropy : S ≤ 43*(c.T : ℝ)*Q := tuned_entropy_bound q hG hR hε
  have hnoise := inner_noise_tuning c.α ν q.R Q S (c.T : ℝ) hν.le (by positivity) hproxy hentropy
  have hcap : Real.sqrt V ≤ c.α*c.T/q.R :=
    error_cap_tuning c.α q.R V c.T hα.le hR hV hT hnoise.1
  have hM : 0 < M := by dsimp [M]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ q.R := by
    apply (div_le_iff₀ (show 0 < 192*M by positivity)).mpr
    have he : q.R*M = q.R*q.G+c.α*c.T := by dsimp [M]; field_simp
    have hh := mul_le_mul_of_nonneg_left hT hα.le
    nlinarith
  have hlog : Real.log (q.R/r) ≤ 20*Q := by
    apply density_log_bound q.R q.G c.α c.T Q (q.G*q.R/q.ε) hR hα hG.le hT hQ (by positivity)
    · change q.R*q.G/(q.ε/8) = 8*(q.G*q.R/q.ε)
      ring
    · exact tuned_inner_log_bound q hG hR hε
    · exact (logScale_component_bounds q hG hR hε).2
  have hiter := density_iterations_tuning (q.m : ℝ) c.T Q (Real.log (q.R/r)) (Nat.cast_nonneg _) hQ
    (tuned_inner_count_bounds q hG hR hε).1 hlog
  have hrM : 2*r*M ≤ c.α/96 := by
    have he : 2*r*M = c.α/96 := by dsimp [r]; field_simp; ring
    exact he.le
  have hn : 256*(1+q.R*q.G/c.α+(c.T : ℝ)) ≤ c.n := by
    have hh := Nat.le_ceil (256*(1+8*q.R*q.G/q.ε+(c.T : ℝ)))
    change 256*(1+q.R*q.G/(q.ε/8)+(c.T : ℝ)) ≤ ⌈256*(1+8*q.R*q.G/q.ε+(c.T : ℝ))⌉₊
    convert hh using 1
    ring
  have hgrid := grid_margin_tuning c.α q.R q.G hα hR hG.le c.T c.n hc.2.2.2.1 hn
  change 0 ≤ V ∧ 0 ≤ W ∧ q.G+Real.sqrt V ≤ M ∧ 0 < r ∧ r ≤ q.R ∧
    (q.m : ℝ)*Real.log (q.R/r) ≤ (c.T : ℝ)/48 ∧ 2*r*M ≤ c.α/96 ∧
    (c.α/2+2*q.R*M)*c.T/c.n ≤ c.α*c.T/32 ∧ 2*(q.R^2*V+W)*c.T ≤ (c.α*c.T/32)^2
  exact ⟨hV,hW,by dsimp [M]; linarith,hr,hrR,by linarith,hrM,hgrid,hnoise.2⟩

end LongTails.Proofs.SpikedSoftCutTuning
