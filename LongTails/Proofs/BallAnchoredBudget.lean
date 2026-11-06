import LongTails.Proofs.BallAnchoredExecution
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.BallAnchoredBudget

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredOuter
open LongTails.Proofs.BallAnchoredSearchRun
open LongTails.Proofs.BallAnchoredExecution

noncomputable section

lemma log2_nat_le {m : ℕ} {W : ℝ} {n : ℕ} (hW : 1 ≤ W) (h : (m : ℝ) ≤ W ^ n) :
    (Nat.log2 m : ℝ) ≤ n * Real.log W / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · rw [h0, Nat.log2_eq_log_two, Nat.log_zero_right, Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hW)
  · have hp : 2 ^ Nat.log2 m ≤ m := by
      rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 hm.ne'
    have hp1 : ((2 ^ Nat.log2 m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hp
    push_cast at hp1
    have hp' : (2 : ℝ) ^ Nat.log2 m ≤ W ^ n := hp1.trans h
    have := Real.log_le_log (by positivity) hp'
    rw [Real.log_pow, Real.log_pow] at this
    linarith

lemma log2_ceil_le {X W : ℝ} {n : ℕ} (hX : 0 ≤ X) (hW : 1 ≤ W) (h : X + 1 ≤ W ^ n) :
    (Nat.log2 ⌈X⌉₊ : ℝ) ≤ n * Real.log W / Real.log 2 := by
  apply log2_nat_le hW
  exact (Nat.ceil_lt_add_one hX).le.trans h

variable (p : Public) (Λ : ℝ)

def side : ℝ := p.D + 1 / p.M

def cplx : ℝ := p.M * Λ * side p ^ 2 / p.ε

def base : ℝ := 3 + p.M * p.D + cplx p Λ

structure Pos : Prop where
  M : 0 < p.M
  D : 0 < p.D
  ε : 0 < p.ε
  Λ : 0 ≤ Λ

variable {p Λ}

lemma side_pos (h : Pos p Λ) : 0 < side p := by
  unfold side; have := h.M; have := h.D; positivity

lemma M_side (h : Pos p Λ) : p.M * side p = p.M * p.D + 1 := by
  unfold side; rw [mul_add, mul_one_div_cancel h.M.ne']

lemma cplx_nonneg (h : Pos p Λ) : 0 ≤ cplx p Λ := by
  unfold cplx; have := h.M; have := h.ε; have := h.Λ; positivity

lemma base_ge (h : Pos p Λ) : 3 ≤ base p Λ := by
  unfold base; have := cplx_nonneg h; have := h.M; have := h.D; nlinarith [mul_pos h.M h.D]

lemma cplx_le_base (h : Pos p Λ) : cplx p Λ ≤ base p Λ := by
  unfold base; have := mul_pos h.M h.D; linarith

lemma md_le_base (h : Pos p Λ) : 1 + p.M * p.D ≤ base p Λ := by
  unfold base; have := cplx_nonneg h; linarith

lemma log_base_ge (h : Pos p Λ) : 1 ≤ Real.log (base p Λ) := by
  have h3 := base_ge h
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (he.trans h3)

lemma log_base_le (h : Pos p Λ) : Real.log (base p Λ) ≤ base p Λ := by
  have := Real.log_le_sub_one_of_pos (by linarith [base_ge h] : 0 < base p Λ)
  linarith

lemma pow_base {k : ℕ} (h : Pos p Λ) (c : ℝ) (hc : c ≤ 3 ^ k) :
    c * base p Λ ≤ base p Λ ^ k * base p Λ := by
  have h3 := base_ge h
  have : (3 : ℝ) ^ k ≤ base p Λ ^ k := pow_le_pow_left₀ (by norm_num) h3 k
  exact mul_le_mul_of_nonneg_right (hc.trans this) (by linarith)

lemma stepMax_le (h : Pos p Λ) : stepMax p ≤ 2 * side p / p.ε := by
  unfold stepMax side radius
  apply div_le_div_of_nonneg_right _ h.ε.le
  have hMi : 0 < 1 / p.M := by have := h.M; positivity
  have h8 : 1 / (8 * p.M) = 1 / 8 * (1 / p.M) := (one_div_mul_one_div 8 p.M).symm
  linarith

lemma rho_le (h : Pos p Λ) : rho p ≤ 3 * side p := by
  unfold rho side radius
  have hMi : 0 < 1 / p.M := by have := h.M; positivity
  have h8 : 1 / (8 * p.M) = 1 / 8 * (1 / p.M) := (one_div_mul_one_div 8 p.M).symm
  linarith

lemma twoD_le (h : Pos p Λ) : 2 * p.D + radius p ≤ 2 * side p := by
  unfold side radius
  have hMi : 0 < 1 / p.M := by have := h.M; positivity
  have h8 : 1 / (8 * p.M) = 1 / 8 * (1 / p.M) := (one_div_mul_one_div 8 p.M).symm
  linarith

lemma MΛρs_le (h : Pos p Λ) : p.M * Λ * rho p * stepMax p ≤ 6 * cplx p Λ := by
  have hM := h.M; have hΛ := h.Λ; have hε := h.ε
  have hs := side_pos h
  have h1 := rho_le h
  have h2 := stepMax_le h
  have hρ : 0 ≤ rho p := by unfold rho radius; have := h.D; positivity
  have hs0 : 0 ≤ stepMax p := by unfold stepMax radius; have := h.D; positivity
  calc p.M * Λ * rho p * stepMax p ≤ p.M * Λ * (3 * side p) * (2 * side p / p.ε) := by
        gcongr
    _ = 6 * cplx p Λ := by unfold cplx; ring

lemma Λs_le (h : Pos p Λ) : Λ * stepMax p ≤ 2 * cplx p Λ := by
  have hM := h.M; have hΛ := h.Λ; have hε := h.ε
  have hs := side_pos h
  have h2 := stepMax_le h
  have hMs := M_side h
  have hMD := mul_pos h.M h.D
  calc Λ * stepMax p ≤ Λ * (2 * side p / p.ε) := mul_le_mul_of_nonneg_left h2 hΛ
    _ ≤ (p.M * side p) * (Λ * (2 * side p / p.ε)) := by
      have : 0 ≤ Λ * (2 * side p / p.ε) := by positivity
      nlinarith
    _ = 2 * cplx p Λ := by unfold cplx; ring

lemma halt_le (h : Pos p Λ) :
    (haltBound p Λ : ℝ) ≤ 6 * Real.log (base p Λ) / Real.log 2 := by
  unfold haltBound
  have hM := h.M
  have hr : radius p = 1 / (8 * p.M) := rfl
  have hX : 24 * Λ * rho p * stepMax p / (7 * radius p) =
      192 / 7 * (p.M * Λ * rho p * stepMax p) := by
    rw [hr]; field_simp; ring
  have h1 := MΛρs_le h
  have hc := cplx_nonneg h
  have hb := cplx_le_base h
  have h3 := base_ge h
  have hρ : 0 ≤ rho p := by unfold rho radius; have := h.D; positivity
  have hs0 : 0 ≤ stepMax p := by unfold stepMax radius; have := h.D; have := h.ε; positivity
  have hX0 : 0 ≤ 24 * Λ * rho p * stepMax p / (7 * radius p) := by
    rw [hX]; have := h.Λ; positivity
  have := log2_ceil_le (n := 6) hX0 (by linarith) (by
    have hp := pow_base (k := 5) h 166 (by norm_num)
    rw [hX, show base p Λ ^ 6 = base p Λ ^ 5 * base p Λ by ring]
    linarith)
  exact_mod_cast this

lemma log_ratio_le (h : Pos p Λ) : logRatio p Λ ≤ 7 * Real.log (base p Λ) := by
  unfold logRatio
  have hM := h.M
  have hr : radius p = 1 / (8 * p.M) := rfl
  have hX : 48 * Λ * rho p * stepMax p / (7 * radius p) =
      384 / 7 * (p.M * Λ * rho p * stepMax p) := by
    rw [hr]; field_simp; ring
  have h1 := MΛρs_le h
  have hc := cplx_nonneg h
  have hb := cplx_le_base h
  have h3 := base_ge h
  have hρ : 0 ≤ rho p := by unfold rho radius; have := h.D; positivity
  have hs0 : 0 ≤ stepMax p := by unfold stepMax radius; have := h.D; have := h.ε; positivity
  have hpos : 0 < 1 + 48 * Λ * rho p * stepMax p / (7 * radius p) := by
    rw [hX]; have := h.Λ; positivity
  have hp := pow_base (k := 6) h 331 (by norm_num)
  have hle : 1 + 48 * Λ * rho p * stepMax p / (7 * radius p) ≤ base p Λ ^ 7 := by
    rw [hX, show base p Λ ^ 7 = base p Λ ^ 6 * base p Λ by ring]
    linarith
  have := Real.log_le_log hpos hle
  rw [Real.log_pow] at this
  exact_mod_cast this

lemma lip_arg_le (h : Pos p Λ) :
    6 * lipBound p Λ * stepMax p / radius p + 1 ≤ base p Λ ^ 14 := by
  have hM := h.M; have hΛ := h.Λ
  have hr : radius p = 1 / (8 * p.M) := rfl
  have h1 := MΛρs_le h
  have h2 := Λs_le h
  have hc := cplx_nonneg h
  have hb := cplx_le_base h
  have h3 := base_ge h
  have hmd := md_le_base h
  have hρ : 0 ≤ rho p := by unfold rho radius; have := h.D; positivity
  have hs0 : 0 ≤ stepMax p := by unfold stepMax radius; have := h.D; have := h.ε; positivity
  have h2D := twoD_le h
  have hMs := M_side h
  have hq : p.M * (2 * p.D + radius p) ≤ 2 * (1 + p.M * p.D) := by
    have := mul_le_mul_of_nonneg_left h2D hM.le
    rw [show p.M * (2 * side p) = 2 * (p.M * side p) by ring, hMs] at this
    linarith
  have e : 6 * lipBound p Λ * stepMax p / radius p =
      96 * (p.M * Λ * rho p * stepMax p) + 48 * (p.M * Λ * rho p * stepMax p) *
        (Λ * stepMax p) * (384 / 7 * (p.M * (2 * p.D + radius p)) + 1) := by
    unfold lipBound; rw [hr]; field_simp; ring
  rw [e]
  have hA : 0 ≤ p.M * Λ * rho p * stepMax p := by positivity
  have hB : 0 ≤ Λ * stepMax p := by positivity
  have hC : 384 / 7 * (p.M * (2 * p.D + radius p)) + 1 ≤ 111 * base p Λ := by
    have : (1 : ℝ) ≤ base p Λ := by linarith
    nlinarith
  have hAB : (p.M * Λ * rho p * stepMax p) * (Λ * stepMax p) ≤ 12 * base p Λ ^ 2 := by
    have := mul_le_mul h1 h2 hB (by positivity)
    nlinarith
  have hb0 : 0 ≤ base p Λ := by linarith
  have hW3 : 64513 * base p Λ ^ 3 ≤ base p Λ ^ 14 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 11
    rw [show base p Λ ^ 14 = base p Λ ^ 11 * base p Λ ^ 3 by ring]
    have : (64513 : ℝ) ≤ 3 ^ 11 := by norm_num
    nlinarith [pow_nonneg hb0 3, pow_nonneg hb0 11]
  have hC0 : 0 ≤ 384 / 7 * (p.M * (2 * p.D + radius p)) + 1 := by
    have : 0 < radius p := by rw [hr]; positivity
    have := h.D; positivity
  have hbig : 48 * (p.M * Λ * rho p * stepMax p) * (Λ * stepMax p) *
      (384 / 7 * (p.M * (2 * p.D + radius p)) + 1) ≤ 48 * (12 * base p Λ ^ 2) * (111 * base p Λ) := by
    have := mul_le_mul hAB hC hC0 (by positivity)
    nlinarith
  have hW1 : base p Λ ≤ base p Λ ^ 3 := by nlinarith [pow_nonneg hb0 2]
  have hW2 : base p Λ ^ 2 ≤ base p Λ ^ 3 := by nlinarith [pow_nonneg hb0 2]
  have hW0 : 1 ≤ base p Λ ^ 3 := by nlinarith [pow_nonneg hb0 2]
  nlinarith

lemma bis_le (h : Pos p Λ) :
    (bisBound p Λ : ℝ) ≤ 14 * Real.log (base p Λ) / Real.log 2 := by
  unfold bisBound
  have hr : 0 < radius p := by unfold radius; have := h.M; positivity
  have hX0 : 0 ≤ 6 * lipBound p Λ * stepMax p / radius p := by
    unfold lipBound
    have hρ : 0 ≤ rho p := by unfold rho; have := h.D; positivity
    have hs0 : 0 ≤ stepMax p := by unfold stepMax; have := h.D; have := h.ε; positivity
    have := h.Λ; have := h.D
    positivity
  have := log2_ceil_le (n := 14) hX0 (by linarith [base_ge h]) (lip_arg_le h)
  exact_mod_cast this

lemma cube_root_eq {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ ((1 : ℝ) / 3) = x := by
  rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

lemma md_rpow_cube (h : Pos p Λ) :
    ((p.M * p.D) ^ ((2 : ℝ) / 3)) ^ 3 = (p.M * p.D) ^ 2 := by
  have hmd : 0 ≤ p.M * p.D := (mul_pos h.M h.D).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul hmd]
  norm_num

lemma outer_le (h : Pos p Λ) :
    (outerBound p Λ : ℝ) ≤ 32 * (p.M * p.D) ^ ((2 : ℝ) / 3) * Real.log (base p Λ) + 1 := by
  unfold outerBound
  have hL := log_ratio_le h
  have hℓ1 := log_base_ge h
  have hy3 := md_rpow_cube h
  set y := (p.M * p.D) ^ ((2 : ℝ) / 3) with hy
  set ℓ := Real.log (base p Λ) with hℓ
  have hmd : 0 ≤ p.M * p.D := (mul_pos h.M h.D).le
  have hy0 : 0 ≤ y := Real.rpow_nonneg hmd _
  have hL0 : 0 ≤ logRatio p Λ := by
    unfold logRatio
    apply Real.log_nonneg
    have hρ : 0 ≤ rho p := by unfold rho radius; have := h.D; have := h.M; positivity
    have hs0 : 0 ≤ stepMax p := by unfold stepMax radius; have := h.D; have := h.ε; have := h.M; positivity
    have hr : 0 < radius p := by unfold radius; have := h.M; positivity
    have := h.Λ
    have : 0 ≤ 48 * Λ * rho p * stepMax p / (7 * radius p) := by positivity
    linarith
  have hL2 : logRatio p Λ ^ 2 ≤ 49 * ℓ ^ 2 := by nlinarith
  have hdec : p.D ^ 2 / (2 * decrement p) = 3072 / 5 * (p.M * p.D) ^ 2 := by
    unfold decrement radius; have := h.M.ne'; field_simp; ring
  set X := logRatio p Λ ^ 2 * (p.D ^ 2 / (2 * decrement p)) with hX
  have hX0 : 0 ≤ X := by rw [hX, hdec]; positivity
  have hXle : X ≤ (32 * y * ℓ) ^ 3 := by
    rw [hX, hdec]
    have e : (32 * y * ℓ) ^ 3 = 32768 * (p.M * p.D) ^ 2 * ℓ ^ 3 := by rw [← hy3]; ring
    rw [e]
    have hℓ3 : ℓ ^ 2 ≤ ℓ ^ 3 := by nlinarith
    have hmd2 : 0 ≤ (p.M * p.D) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hL2 hmd2, mul_le_mul_of_nonneg_left hℓ3 hmd2]
  have hroot : X ^ ((1 : ℝ) / 3) ≤ 32 * y * ℓ := by
    have := Real.rpow_le_rpow hX0 hXle (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [cube_root_eq (by positivity)] at this
  have hfl := Nat.floor_le (Real.rpow_nonneg hX0 ((1 : ℝ) / 3))
  push_cast
  linarith

lemma outer_succ_le (h : Pos p Λ) : ((outerBound p Λ + 1 : ℕ) : ℝ) ≤ base p Λ ^ 6 := by
  have h1 := outer_le h
  have hmd : 0 ≤ p.M * p.D := (mul_pos h.M h.D).le
  set y := (p.M * p.D) ^ ((2 : ℝ) / 3) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hmd _
  have hy3 : y ^ 3 = (p.M * p.D) ^ 2 := md_rpow_cube h
  have hb3 := base_ge h
  have hb0 : 0 ≤ base p Λ := by linarith
  have hyW : y ≤ base p Λ := by
    have h2 : y ≤ 1 + p.M * p.D := by
      have : y ^ 3 ≤ (1 + p.M * p.D) ^ 3 := by rw [hy3]; nlinarith [sq_nonneg (p.M * p.D)]
      exact (pow_le_pow_iff_left₀ hy0 (by positivity) (by norm_num)).mp this
    linarith [md_le_base h]
  have hℓW := log_base_le h
  have hℓ0 : 0 ≤ Real.log (base p Λ) := by linarith [log_base_ge h]
  have h6 : 34 * base p Λ ^ 2 ≤ base p Λ ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 4
    rw [show base p Λ ^ 6 = base p Λ ^ 4 * base p Λ ^ 2 by ring]
    nlinarith [pow_nonneg hb0 2]
  push_cast
  nlinarith [mul_le_mul hyW hℓW hℓ0 hb0]

lemma newton_le (h : Pos p Λ) :
    (newtonCount (outerBound p Λ) (stepMax p) Λ : ℝ) ≤ 36 * Real.log (base p Λ) := by
  unfold newtonCount
  have hl2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hℓ1 := log_base_ge h
  have h1 := log2_nat_le (n := 6) (by linarith [base_ge h]) (outer_succ_le h)
  have hs0 : 0 ≤ stepMax p := by unfold stepMax radius; have := h.D; have := h.ε; have := h.M; positivity
  have hX0 : 0 ≤ 1 + 4 * stepMax p * Λ := by have := h.Λ; positivity
  have h2 := log2_ceil_le (n := 3) (W := base p Λ) hX0 (by linarith [base_ge h]) (by
    have := Λs_le h
    have hb := cplx_le_base h
    have hb3 := base_ge h
    have hp := pow_base (k := 2) h 8 (by norm_num)
    have hW : 3 + cplx p Λ ≤ base p Λ := by unfold base; have := mul_pos h.M h.D; linarith
    rw [show base p Λ ^ 3 = base p Λ ^ 2 * base p Λ by ring]
    nlinarith)
  push_cast
  have hinv : Real.log (base p Λ) / Real.log 2 ≤ 1.45 * Real.log (base p Λ) := by
    rw [div_le_iff₀ hl2p]; nlinarith
  have e1 : ((6 : ℕ) : ℝ) * Real.log (base p Λ) / Real.log 2 =
      6 * (Real.log (base p Λ) / Real.log 2) := by push_cast; ring
  have e2 : ((3 : ℕ) : ℝ) * Real.log (base p Λ) / Real.log 2 =
      3 * (Real.log (base p Λ) / Real.log 2) := by push_cast; ring
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

lemma total_le (h : Pos p Λ) :
    (totalBound p Λ : ℝ) ≤ 2 ^ 17 * (1 + (p.M * p.D) ^ ((2 : ℝ) / 3)) *
      Real.log (base p Λ) ^ 3 := by
  unfold totalBound roundBound tickMax
  have hl2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hH := halt_le h
  have hJ := bis_le h
  have hO := outer_le h
  have hN := newton_le h
  have hℓ1 := log_base_ge h
  set ℓ := Real.log (base p Λ) with hℓ
  have hinv : ℓ / Real.log 2 ≤ 1.45 * ℓ := by
    rw [div_le_iff₀ hl2p]; nlinarith
  set y := (p.M * p.D) ^ ((2 : ℝ) / 3) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (mul_pos h.M h.D).le _
  have e1 : 6 * ℓ / Real.log 2 = 6 * (ℓ / Real.log 2) := by ring
  have e2 : 14 * ℓ / Real.log 2 = 14 * (ℓ / Real.log 2) := by ring
  rw [e1] at hH
  rw [e2] at hJ
  have hHJ : (haltBound p Λ : ℝ) + bisBound p Λ + 3 ≤ 32 * ℓ := by nlinarith
  have hT : 2 * (newtonCount (outerBound p Λ) (stepMax p) Λ : ℝ) + 1 ≤ 73 * ℓ := by nlinarith
  have hO1 : (outerBound p Λ : ℝ) + 1 ≤ 34 * (1 + y) * ℓ := by nlinarith
  push_cast
  have hA : 0 ≤ (outerBound p Λ : ℝ) + 1 := by positivity
  have hB : 0 ≤ (haltBound p Λ : ℝ) + bisBound p Λ + 3 := by positivity
  have hC : 0 ≤ 2 * (newtonCount (outerBound p Λ) (stepMax p) Λ : ℝ) + 1 := by positivity
  calc ((outerBound p Λ : ℝ) + 1) * (((haltBound p Λ : ℝ) + bisBound p Λ + 3) *
        (2 * (newtonCount (outerBound p Λ) (stepMax p) Λ : ℝ) + 1))
      ≤ (34 * (1 + y) * ℓ) * ((32 * ℓ) * (73 * ℓ)) := by
        apply mul_le_mul hO1 _ (by positivity) (by positivity)
        exact mul_le_mul hHJ hT hC (by positivity)
    _ = 79424 * (1 + y) * ℓ ^ 3 := by ring
    _ ≤ 2 ^ 17 * (1 + y) * ℓ ^ 3 := by
        have : 0 ≤ (1 + y) * ℓ ^ 3 := by positivity
        nlinarith

end

end LongTails.Proofs.BallAnchoredBudget
