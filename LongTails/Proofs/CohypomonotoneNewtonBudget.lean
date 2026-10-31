import LongTails.Algorithms.CohypomonotoneNewton
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.CohypomonotoneNewtonBudget

open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton

universe u

lemma horizon_growth (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    25165824 * (p.H * p.R ^ 2 / p.ε) ^ 2 < (horizon p : ℝ) ^ 5 := by
  let Q := p.H * p.R ^ 2 / p.ε
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hS : 0 ≤ 1 + Q := by positivity
  have hc : 64 * (1 + Q) ^ (2 / 5 : ℝ) ≤ (horizon p : ℝ) := Nat.le_ceil _
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 64 * (1 + Q) ^ (2 / 5 : ℝ)) hc 5
  have he : ((1 + Q) ^ (2 / 5 : ℝ)) ^ (5 : ℕ) = (1 + Q) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
    norm_num
  rw [mul_pow, he] at hp
  change 25165824 * Q ^ 2 < _
  nlinarith [sq_nonneg Q]

lemma horizon_upper (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    (horizon p : ℝ) ≤ 65 * (1 + p.H * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) := by
  let S := 1 + p.H * p.R ^ 2 / p.ε
  have hS : 1 ≤ S := by
    have hh : 0 ≤ p.H * p.R ^ 2 / p.ε := by positivity
    dsimp [S]
    linarith
  have hr : 1 ≤ S ^ (2 / 5 : ℝ) := Real.one_le_rpow hS (by norm_num)
  have hc : (horizon p : ℝ) < 64 * S ^ (2 / 5 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

lemma terminal_step_accuracy {a H R ε g : ℝ} (hH : 0 < H)
    (hε : 0 < ε) (ha : 0 < a) (haR : 16 * R / ε ≤ a)
    (haH : 2 / Real.sqrt (H * ε) ≤ a)
    (hg : g ≤ 5 * R / a + 5 / (64 * H * a ^ 2)) : g ≤ ε := by
  have hs : 0 < Real.sqrt (H * ε) := Real.sqrt_pos.mpr (mul_pos hH hε)
  have hs2 := Real.sq_sqrt (mul_pos hH hε).le
  have h1 : 16 * R ≤ a * ε := (div_le_iff₀ hε).mp haR
  have h2 : 2 ≤ a * Real.sqrt (H * ε) := (div_le_iff₀ hs).mp haH
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
  rw [mul_pow, hs2] at h3
  have h4 : 5 * R / a ≤ 5 * ε / 16 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [h1]
  have h5 : 5 / (64 * H * a ^ 2) ≤ 5 * ε / 256 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * H * a ^ 2)).mpr
    nlinarith only [h3]
  linarith

lemma maxStep_scaled (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    p.H * p.R * maxStep p ≤ 18 * (1 + p.H * p.R ^ 2 / p.ε) := by
  let Q := p.H * p.R ^ 2 / p.ε
  let t := p.H * p.R / Real.sqrt (p.H * p.ε)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hs : 0 < Real.sqrt (p.H * p.ε) := Real.sqrt_pos.mpr (mul_pos hH hε)
  have hs2 := Real.sq_sqrt (mul_pos hH hε).le
  have ht : t ^ 2 = Q := by
    dsimp [t, Q]
    rw [div_pow, hs2]
    field_simp
  have he : p.H * p.R * maxStep p = 16 * Q + 2 * t + 1 / 128 := by
    dsimp [maxStep, baseStep, Q, t]
    field_simp
  rw [he]
  change 16 * Q + 2 * t + 1 / 128 ≤ 18 * (1 + Q)
  nlinarith [sq_nonneg (t - 1)]

lemma maxStep_ratio (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    maxStep p / baseStep p ≤ 2304 * (1 + p.H * p.R ^ 2 / p.ε) := by
  have hh := maxStep_scaled p hH hR hε
  have he : maxStep p / baseStep p = 128 * (p.H * p.R * maxStep p) := by
    dsimp [baseStep]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [he]
  linarith

lemma power_bound_from_log {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    B ^ n ≤ (2 : ℝ) ^ ⌈2 * (n : ℝ) * (1 + Real.log B)⌉₊ := by
  have hB0 : 0 < B := by linarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  let k := ⌈2 * (n : ℝ) * (1 + Real.log B)⌉₊
  have hc : 2 * (n : ℝ) * (1 + Real.log B) ≤ (k : ℝ) := Nat.le_ceil _
  have hm := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have he : (n : ℝ) * Real.log B ≤ (k : ℝ) * Real.log 2 := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  calc
    B ^ n = Real.exp ((n : ℝ) * Real.log B) := by rw [Real.exp_nat_mul, Real.exp_log hB0]
    _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr he
    _ = 2 ^ k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma search_depth_bounds {B S : ℝ} (hB : 2 ≤ B) (hS : 0 < S) (hSB : S ≤ B) :
    2304 * S ≤ (2 : ℝ) ^ ⌈30 * (1 + Real.log B)⌉₊ ∧
      288000000000 * S ^ 4 < (2 : ℝ) ^ ⌈100 * (1 + Real.log B)⌉₊ := by
  have hB1 : 1 ≤ B := by linarith
  have hg := power_bound_from_log hB1 15
  have hb := power_bound_from_log hB1 50
  norm_num only [Nat.cast_ofNat, mul_assoc] at hg hb
  have hp14 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB 14
  have hmul := mul_le_mul hp14 hSB hS.le (by positivity : (0 : ℝ) ≤ B ^ 14)
  have he15 : B ^ 14 * B = B ^ 15 := by ring
  rw [he15] at hmul
  have hp46 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB 46
  have hp4 := pow_le_pow_left₀ hS.le hSB 4
  have hmul4 := mul_le_mul hp46 hp4 (by positivity : 0 ≤ S ^ 4) (by positivity : 0 ≤ B ^ 46)
  have he50 : B ^ 46 * B ^ 4 = B ^ 50 := by ring
  rw [he50] at hmul4
  constructor
  · nlinarith only [hg, hmul, hS.le]
  · have hs4 : 0 < S ^ 4 := pow_pos hS 4
    nlinarith only [hb, hmul4, hs4]

lemma search_depth_sum {ell : ℝ} (hell : 1 ≤ ell) :
    ⌈30 * ell⌉₊ + ⌈100 * ell⌉₊ + 2 ≤ ⌈200 * ell⌉₊ + 1 := by
  have he0 : 0 ≤ ell := by linarith
  have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 30 * ell)
  have h2 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 100 * ell)
  have h3 : 200 * ell ≤ (⌈200 * ell⌉₊ : ℝ) := Nat.le_ceil _
  have hh : (⌈30 * ell⌉₊ : ℝ) + (⌈100 * ell⌉₊ : ℝ) + 2 ≤
      (⌈200 * ell⌉₊ : ℝ) + 1 := by linarith
  exact_mod_cast hh

lemma public_search_depths (p : Public.{u}) (hH : 0 < p.H) (hρ : 0 ≤ p.ρ)
    (hR : 0 < p.R) (hε : 0 < p.ε) :
    let S := 1 + p.H * p.R ^ 2 / p.ε
    let B := 2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε
    let gap := 1 / (16000000000 * p.H * p.R * S ^ 3)
    let geom := ⌈30 * (1 + Real.log B)⌉₊
    let bis := ⌈100 * (1 + Real.log B)⌉₊
    maxStep p < (2 : ℝ) ^ bis * gap ∧
      maxStep p ≤ (2 : ℝ) ^ geom * baseStep p ∧ geom + bis + 2 ≤ searchFuel p := by
  let S := 1 + p.H * p.R ^ 2 / p.ε
  let B := 2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε
  have hQ : 0 ≤ p.H * p.R ^ 2 / p.ε := by positivity
  have hshift : 0 ≤ shift p := by unfold shift; positivity
  have hq : 0 ≤ shift p * p.H * p.R := by positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hB : 2 ≤ B := by dsimp [B]; linarith
  have hSB : S ≤ B := by dsimp [S, B]; linarith
  have hd := search_depth_bounds hB hS hSB
  have hr := maxStep_ratio p hH hR hε
  have hscaled := maxStep_scaled p hH hR hε
  have hden : 0 < 16000000000 * p.H * p.R * S ^ 3 := by positivity
  have hb : 0 < baseStep p := by unfold baseStep; positivity
  change maxStep p < (2 : ℝ) ^ ⌈100 * (1 + Real.log B)⌉₊ *
      (1 / (16000000000 * p.H * p.R * S ^ 3)) ∧
    maxStep p ≤ (2 : ℝ) ^ ⌈30 * (1 + Real.log B)⌉₊ * baseStep p ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← div_eq_mul_one_div]
    apply (lt_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right hscaled (by positivity : 0 ≤ 16000000000 * S ^ 3)
    change p.H * p.R * maxStep p * (16000000000 * S ^ 3) ≤
      18 * S * (16000000000 * S ^ 3) at hm
    nlinarith only [hm, hd.2]
  · exact (div_le_iff₀ hb).mp (hr.trans hd.1)
  · have hB1 : 1 ≤ B := by linarith
    have hell : 1 ≤ 1 + Real.log B := by linarith [Real.log_nonneg hB1]
    exact search_depth_sum hell

lemma inverseLength_cost {M B tol ell : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (htol : 0 < tol) (hell : 1 ≤ ell) (hlog : Real.log (1 + B / tol) ≤ 30 * ell) :
    ((inverseLength M B tol + 1 : ℕ) : ℝ) ≤ 200 * ell * (1 + M * B) := by
  have hMB : 0 ≤ M * B := mul_nonneg hM hB
  have he : 0 ≤ ell := by linarith
  have hratio : 1 ≤ 1 + B / tol := by have := div_nonneg hB htol.le; linarith
  have hlog0 : 0 ≤ Real.log (1 + B / tol) := Real.log_nonneg hratio
  have hmax : 2 * max 1 (2 * M * B) ≤ 4 * (1 + M * B) := by
    have hm : max 1 (2 * M * B) ≤ 2 * (1 + M * B) := max_le (by linarith) (by linarith)
    linarith
  have hprod := mul_le_mul hmax hlog hlog0 (by positivity : 0 ≤ 4 * (1 + M * B))
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * max 1 (2 * M * B) * Real.log (1 + B / tol) by positivity)
  have hcast : ((inverseLength M B tol + 1 : ℕ) : ℝ) =
      (⌈2 * max 1 (2 * M * B) * Real.log (1 + B / tol)⌉₊ : ℝ) + 2 := by
    simp only [inverseLength, Nat.cast_add, Nat.cast_one]
    ring
  rw [hcast]
  have hm := mul_nonneg he hMB
  nlinarith only [hc, hprod, hm, hell]

lemma amortization_absorption {q S : ℝ} (hq : 1 ≤ q) (hS : 1 ≤ S) :
    q * (1 + Real.log (1 + q + S)) ≤ 4 * q ^ 2 + 13 * S ^ (2 / 5 : ℝ) := by
  have hq0 : 0 < q := by linarith
  have hS0 : 0 < S := by linarith
  have hprod : 1 + q + S ≤ (1 + q) * (1 + S) := by nlinarith [mul_nonneg hq0.le hS0.le]
  have hlogprod := Real.log_le_log (by positivity : 0 < 1 + q + S) hprod
  rw [Real.log_mul (by positivity : (1 : ℝ) + q ≠ 0) (by positivity : (1 : ℝ) + S ≠ 0)] at hlogprod
  have hlogq := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + q)
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) < 1 + S)
    (show 1 + S ≤ 2 * S by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hS0.ne'] at hlogs
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogpow := Real.log_le_rpow_div hS0.le (by norm_num : (0 : ℝ) < 1 / 5)
  have hell : 1 + Real.log (1 + q + S) ≤ 2 + q + 5 * S ^ (1 / 5 : ℝ) := by
    norm_num at hlogpow
    linarith
  have ht : (S ^ (1 / 5 : ℝ)) ^ (2 : ℕ) = S ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]
    norm_num
  have hp := mul_le_mul_of_nonneg_left hell hq0.le
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hy := sq_nonneg (q - 5 / 2 * S ^ (1 / 5 : ℝ))
  have hr : 0 ≤ S ^ (2 / 5 : ℝ) := Real.rpow_nonneg hS0.le _
  nlinarith only [hp, hq2, hy, ht, hr]

lemma center_lipschitz_constants (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R)
    {A : ℝ} (hA : baseStep p ≤ A) :
    4 * p.R / A ≤ 512 * p.H * p.R ^ 2 ∧ 8 * p.R / A ≤ 1024 * p.H * p.R ^ 2 := by
  have hb : 0 < baseStep p := by unfold baseStep; positivity
  have hA0 : 0 < A := hb.trans_le hA
  have hm := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 512 * p.H * p.R ^ 2)
  have he : 512 * p.H * p.R ^ 2 * baseStep p = 4 * p.R := by unfold baseStep; field_simp; norm_num
  rw [he] at hm
  constructor
  · exact (div_le_iff₀ hA0).mpr hm
  · apply (div_le_iff₀ hA0).mpr
    nlinarith only [hm]

lemma affine_path_constant {H R amax : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R) (ha : 0 ≤ amax) :
    512 * H * R ^ 2 + 7 * (H * R) * R + (H * R) * (10 * (H * R * amax) * R) +
      amax * (2 * (H * R) + H * (10 * (H * R * amax) * R)) * (1024 * H * R ^ 2) ≤
      20000 * H * R ^ 2 * (1 + H * R * amax) ^ 2 := by
  have hU : 0 ≤ H * R * amax := by positivity
  have hp : 519 + 2058 * (H * R * amax) + 10240 * (H * R * amax) ^ 2 ≤
      20000 * (1 + H * R * amax) ^ 2 := by nlinarith [sq_nonneg (H * R * amax)]
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ H * R ^ 2)
  nlinarith only [hm]

lemma merit_path_constant {H R amax : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R) (ha : 0 ≤ amax) :
    H * (10 * (H * R * amax) * R +
      amax * (20000 * H * R ^ 2 * (1 + H * R * amax) ^ 2 + 1024 * H * R ^ 2)) ≤
      23000 * H * R * (1 + H * R * amax) ^ 3 := by
  have hU : 0 ≤ H * R * amax := by positivity
  have hp : 10 * (H * R * amax) +
      (H * R * amax) * (20000 * (1 + H * R * amax) ^ 2 + 1024) ≤
      23000 * (1 + H * R * amax) ^ 3 := by
    nlinarith [sq_nonneg (H * R * amax), pow_nonneg hU 3]
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hH hR)
  nlinarith only [hm]

lemma public_merit_path_constant (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    23000 * p.H * p.R * (1 + p.H * p.R * maxStep p) ^ 3 ≤
      160000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3 := by
  let S := 1 + p.H * p.R ^ 2 / p.ε
  have hS : 1 ≤ S := by
    have hh : 0 ≤ p.H * p.R ^ 2 / p.ε := by positivity
    dsimp [S]
    linarith
  have hU := maxStep_scaled p hH hR hε
  have hstep : 0 ≤ maxStep p := by unfold maxStep baseStep; positivity
  have hh : 1 + p.H * p.R * maxStep p ≤ 19 * S := by change _ ≤ 18 * S at hU; linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + p.H * p.R * maxStep p) hh 3
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 23000 * p.H * p.R)
  have hs3 : 0 ≤ p.H * p.R * S ^ 3 := by positivity
  change _ ≤ 160000000 * p.H * p.R * S ^ 3
  nlinarith only [hm, hs3]

lemma scaled_small_tolerance {a H d : ℝ} (ha : 0 < a) (hH : 0 < H)
    (hd : d ≤ 1 / (4096 * H * a)) : a * H * d ≤ 1 / 4096 := by
  have hh := mul_le_mul_of_nonneg_left hd (mul_pos ha hH).le
  have he : a * H * (1 / (4096 * H * a)) = 1 / 4096 := by field_simp
  exact hh.trans_eq he

lemma scaled_endpoint_tolerance {a L e d : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hd : d ≤ e / (64 * (1 + a * L))) : (1 + a * L) * d ≤ e / 64 := by
  have hscale : 0 < 1 + a * L := by positivity
  have hh := mul_le_mul_of_nonneg_left hd hscale.le
  have he : (1 + a * L) * (e / (64 * (1 + a * L))) = e / 64 := by field_simp
  exact hh.trans_eq he

lemma tolerance_floor_scalar {A a H R S k : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hH : 0 < H) (hR : 0 < R) (hS : 1 ≤ S)
    (hk : 0 < k) (hB : (A + a) / a ≤ 4608 * S) (hkS : k ≤ 66 * S)
    (haS : a * H * R ≤ 18 * S) :
    R / (400000000 * S ^ 3) ≤
      min (((a / (A + a)) * R / k) / (64 * (1 + a * H * R))) (1 / (4096 * H * a)) := by
  have hS0 : 0 < S := by linarith
  have hsum : 0 < A + a := by positivity
  have hden : 0 < 64 * ((A + a) / a) * k * (1 + a * H * R) := by positivity
  have hd : 64 * ((A + a) / a) * k * (1 + a * H * R) ≤ 400000000 * S ^ 3 := by
    calc
      _ ≤ 64 * (4608 * S) * (66 * S) * (19 * S) := by
        gcongr
        linarith
      _ ≤ _ := by nlinarith [pow_nonneg hS0.le 3]
  have hfrac := div_le_div_of_nonneg_left hR.le hden hd
  have hid : R / (64 * ((A + a) / a) * k * (1 + a * H * R)) =
      ((a / (A + a)) * R / k) / (64 * (1 + a * H * R)) := by field_simp
  rw [hid] at hfrac
  refine le_min hfrac ?_
  have hpow : S ≤ S ^ 3 := le_self_pow₀ hS (by decide)
  have hdsmall : 4096 * H * a * R ≤ 400000000 * S ^ 3 := by
    nlinarith only [haS, hpow, hS]
  have hh := div_le_div_of_nonneg_left hR.le (by positivity : 0 < 4096 * H * a * R) hdsmall
  have he : R / (4096 * H * a * R) = 1 / (4096 * H * a) := by field_simp
  rwa [he] at hh

lemma inverse_log_bound {q S R B tol : ℝ} (hq : 1 ≤ q) (hS : 1 ≤ S) (hR : 0 < R)
    (hB : 0 ≤ B) (hupper : B ≤ 8 * q * R)
    (htol : R / (400000000 * S ^ 3) ≤ tol) :
    Real.log (1 + B / tol) ≤ 30 * (1 + Real.log (1 + q + S)) := by
  have hq0 : 0 < q := by linarith
  have hS0 : 0 < S := by linarith
  have ht : 0 < tol := lt_of_lt_of_le (by positivity) htol
  have hr : B / tol ≤ 3200000000 * q * S ^ 3 := by
    have hh1 := div_le_div_of_nonneg_right hupper ht.le
    have hh2 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 8 * q * R)
      (by positivity : 0 < R / (400000000 * S ^ 3)) htol
    have hh := hh1.trans hh2
    have he : (8 * q * R) / (R / (400000000 * S ^ 3)) = 3200000000 * q * S ^ 3 := by field_simp; ring
    rwa [he] at hh
  let T := 1 + q + S
  have hT : 3 ≤ T := by dsimp [T]; linarith
  have hT0 : 0 < T := by linarith
  have hqT : q ≤ T := by dsimp [T]; linarith
  have hST : S ≤ T := by dsimp [T]; linarith
  have hp : q * S ^ 3 ≤ T ^ 4 := by
    calc
      _ ≤ T * T ^ 3 := by gcongr
      _ = _ := by ring
  have hp4 : 1 ≤ T ^ 4 := one_le_pow₀ (by linarith : 1 ≤ T)
  have hp20 : (3 : ℝ) ^ 20 ≤ T ^ 20 := pow_le_pow_left₀ (by norm_num) hT 20
  have hupper' : 1 + B / tol ≤ T ^ 24 := by
    calc
      _ ≤ 3200000001 * T ^ 4 := by nlinarith only [hr, hp, hp4]
      _ ≤ 3 ^ 20 * T ^ 4 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hT0.le 4)
      _ ≤ T ^ 20 * T ^ 4 := mul_le_mul_of_nonneg_right hp20 (pow_nonneg hT0.le 4)
      _ = _ := by rw [← pow_add]
  have hl := Real.log_le_log (by positivity : 0 < 1 + B / tol) hupper'
  rw [Real.log_pow] at hl
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  change Real.log (1 + B / tol) ≤ 30 * (1 + Real.log T)
  norm_num at hl
  linarith

lemma outer_work_scalar {n fuel ell q r U V : ℝ}
    (hf0 : 0 ≤ fuel) (hell : 1 ≤ ell) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hn : n ≤ 65 * r) (hf : fuel ≤ 202 * ell)
    (hU : U ≤ 14 * ell) (hV : V ≤ 14 * ell) :
    200 * ell * (n * (fuel + 1) + 8 * q * fuel * (V + 2 * U) + 4 * q * U) ≤
      (3000000 * r + 14000000 * q * ell) * ell ^ 2 := by
  have he0 : 0 ≤ ell := by linarith
  have hf1 : fuel + 1 ≤ 203 * ell := by linarith
  have hs : V + 2 * U ≤ 42 * ell := by linarith
  have hfirst := mul_le_mul hn hf1 (by positivity : 0 ≤ fuel + 1) (by positivity : 0 ≤ 65 * r)
  have hsecond := mul_le_mul hf hs (by positivity : 0 ≤ V + 2 * U) (by positivity : 0 ≤ 202 * ell)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond (by positivity : 0 ≤ 8 * q)
  have hthird := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 4 * q)
  have hsum : n * (fuel + 1) + 8 * q * fuel * (V + 2 * U) + 4 * q * U ≤
      13195 * r * ell + 67872 * q * ell ^ 2 + 56 * q * ell := by
    nlinarith only [hfirst, hsecond', hthird]
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 200 * ell)
  have hqgrow := mul_nonneg (by positivity : 0 ≤ q * ell ^ 2) (sub_nonneg.mpr hell)
  have hr0 : 0 ≤ r * ell ^ 2 := by positivity
  have hq0 : 0 ≤ q * ell ^ 3 := by positivity
  nlinarith only [hm, hqgrow, hr0, hq0]

lemma normalized_work_scalar {q r ell : ℝ} (hq : 1 ≤ q) (hr : 0 ≤ r) (hell : 1 ≤ ell)
    (habs : q * ell ≤ 4 * q ^ 2 + 13 * r) :
    1 + 200 * ell * (1 + 3 * q ^ 2) + (3000000 * r + 14000000 * q * ell) * ell ^ 2 ≤
      200000000 * (q ^ 2 + r) * ell ^ 2 := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have he2 : 1 ≤ ell ^ 2 := by nlinarith
  have heg : ell ≤ ell ^ 2 := by nlinarith
  have hone : 1 ≤ q ^ 2 * ell ^ 2 := by nlinarith only [hq2, he2, mul_nonneg (sub_nonneg.mpr hq2) (sub_nonneg.mpr he2)]
  have heq := mul_le_mul_of_nonneg_right hq2 (sq_nonneg ell)
  have hqg := mul_le_mul_of_nonneg_left heg (sq_nonneg q)
  have hi : 1 + 200 * ell * (1 + 3 * q ^ 2) ≤ 1000 * q ^ 2 * ell ^ 2 := by
    nlinarith only [hone, heq, heg, hqg]
  have hm := mul_le_mul_of_nonneg_right habs (by positivity : 0 ≤ 14000000 * ell ^ 2)
  have hqr : 0 ≤ q ^ 2 * ell ^ 2 := by positivity
  have hrr : 0 ≤ r * ell ^ 2 := by positivity
  nlinarith only [hi, hm, hqr, hrr]

end LongTails.Proofs.CohypomonotoneNewtonBudget
