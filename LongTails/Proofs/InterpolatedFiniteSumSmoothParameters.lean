import LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

namespace LongTails.Proofs.InterpolatedFiniteSumSmoothParameters

lemma scale_square (n t : ℕ) (R : ℝ) :
    (R / (Real.sqrt n * t * Real.sqrt t)) ^ 2 = R ^ 2 / ((n : ℝ) * (t : ℝ) ^ 3) := by
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg t)]
  congr 1
  ring

lemma scale_radius (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (R : ℝ) :
    (n : ℝ) * (t : ℝ) ^ 3 * (R / (Real.sqrt n * t * Real.sqrt t)) ^ 2 = R ^ 2 := by
  rw [scale_square n t]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  field_simp

lemma scale_curvature (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (R ε : ℝ) (hR : R ≠ 0) :
    12 * (4 * ε / t) / (R / (Real.sqrt n * t * Real.sqrt t)) ^ 2 =
      48 * n * ε * (t : ℝ) ^ 2 / R ^ 2 := by
  rw [scale_square n t]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  field_simp
  ring

lemma scale_gradient (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 ≤ ε) :
    ((4 * ε / t) / (R / (Real.sqrt n * t * Real.sqrt t))) *
      (1 + 2 * Real.sqrt t) ≤ 12 * ε * Real.sqrt n * t / R := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hns : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hts : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast ht)
  have he : (4 * ε / t) / (R / (Real.sqrt n * t * Real.sqrt t)) =
      4 * ε * Real.sqrt n * Real.sqrt t / R := by
    field_simp
  rw [he]
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hs := Real.sq_sqrt (Nat.cast_nonneg t)
  have hst : Real.sqrt t ≤ t := by nlinarith [sq_nonneg (Real.sqrt t - 1)]
  have hh : Real.sqrt t * (1 + 2 * Real.sqrt t) ≤ 3 * t := by nlinarith only [hs, hst]
  have hmul := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 4 * ε * Real.sqrt n / R by positivity)
  convert hmul using 1 <;> ring

lemma length_bounds (n : ℕ) (hn : 0 < n) (H : ℝ) (hH : 144 * n ≤ H) :
    0 < ⌊Real.sqrt (H / n) / 12⌋₊ ∧
    144 * n * (⌊Real.sqrt (H / n) / 12⌋₊ : ℝ) ^ 2 ≤ H ∧
    Real.sqrt (H / n) / 24 ≤ (⌊Real.sqrt (H / n) / 12⌋₊ : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hH0 : 0 ≤ H := (by positivity : (0 : ℝ) ≤ 144 * n).trans hH
  have hratio : 144 ≤ H / n := (le_div_iff₀ hnR).mpr hH
  have hs := Real.sq_sqrt (div_nonneg hH0 hnR.le)
  have hs0 := Real.sqrt_nonneg (H / n)
  have hx : 1 ≤ Real.sqrt (H / n) / 12 := by nlinarith only [hs, hs0, hratio]
  have ht := Nat.floor_pos.mpr hx
  have hfloor := Nat.floor_le (by positivity : 0 ≤ Real.sqrt (H / n) / 12)
  have hupper := Nat.lt_floor_add_one (Real.sqrt (H / n) / 12)
  have htR : (1 : ℝ) ≤ (⌊Real.sqrt (H / n) / 12⌋₊ : ℝ) := by exact_mod_cast ht
  refine ⟨ht, ?_, ?_⟩
  · have hb : 144 * (⌊Real.sqrt (H / n) / 12⌋₊ : ℝ) ^ 2 ≤ H / n := by
      nlinarith [show (0 : ℝ) ≤ (⌊Real.sqrt (H / n) / 12⌋₊ : ℝ) by positivity]
    have hm := (le_div_iff₀ hnR).mp hb
    nlinarith only [hm]
  · linarith only [hupper, htR]

lemma gradient_tuning (n t : ℕ) (H : ℝ) (hH : 144 ≤ H)
    (ht : 144 * n * (t : ℝ) ^ 2 ≤ H) : 144 * Real.sqrt n * t ≤ H := by
  have hn := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsq : (12 * Real.sqrt n * t) ^ 2 ≤ H := by nlinarith only [ht, hn]
  have h₁ := Real.le_sqrt_of_sq_le hsq
  have hH0 : 0 ≤ H := by linarith
  have hs := Real.sq_sqrt hH0
  have hs0 := Real.sqrt_nonneg H
  have hs12 : 12 ≤ Real.sqrt H := by nlinarith only [hs, hs0, hH]
  have h₂ := mul_nonneg hs0 (sub_nonneg.mpr hs12)
  nlinarith only [h₁, h₂, hs]

lemma dimension_polynomial (n t b : ℕ) (S C : ℝ) (hS : 1 ≤ S)
    (hn : (n : ℝ) ≤ S) (ht : (t : ℝ) ≤ S) (hb : b + 1 ≤ 2 * n * t)
    (hC : 0 ≤ C) (hCb : C ≤ 25600 * n * (t : ℝ) ^ 3) :
    8 * (((n : ℝ) * t) ^ 2 + n * t + (b + 1 : ℕ) * n * t * C) ≤ 2 ^ 19 * S ^ 8 := by
  have hS0 : 0 ≤ S := by linarith
  have hs2 : S ^ 2 ≤ S ^ 8 := pow_le_pow_right₀ hS (by omega)
  have hs4 : S ^ 4 ≤ S ^ 8 := pow_le_pow_right₀ hS (by omega)
  have hnt : (n : ℝ) * t ≤ S ^ 8 := by
    calc
      _ ≤ S * S := mul_le_mul hn ht (Nat.cast_nonneg t) hS0
      _ = S ^ 2 := by ring
      _ ≤ _ := hs2
  have hnt2 : ((n : ℝ) * t) ^ 2 ≤ S ^ 8 := by
    calc
      _ ≤ (S * S) ^ 2 := by gcongr
      _ = S ^ 4 := by ring
      _ ≤ _ := hs4
  have hbR : ((b + 1 : ℕ) : ℝ) ≤ 2 * n * t := by exact_mod_cast hb
  have hlast : ((b + 1 : ℕ) : ℝ) * n * t * C ≤ 51200 * S ^ 8 := by
    calc
      _ ≤ (2 * n * t) * n * t * (25600 * n * (t : ℝ) ^ 3) := by gcongr
      _ = 51200 * (n : ℝ) ^ 3 * (t : ℝ) ^ 5 := by ring
      _ ≤ 51200 * S ^ 3 * S ^ 5 := by gcongr
      _ = _ := by ring
  have hp : 0 ≤ S ^ 8 := by positivity
  norm_num only [show (2 : ℝ) ^ 19 = 524288 by norm_num]
  nlinarith only [hnt, hnt2, hlast, hp]

lemma setup_dimension
    (p : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Params)
    (hp : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.valid p)
    (t b : ℕ) (ht : (t : ℝ) ≤ p.L0 * p.R ^ 2 / p.ε) (hb : b + 1 ≤ 2 * p.n * t)
    (C : ℝ) (hC : 0 ≤ C) (hCb : C ≤ 25600 * p.n * (t : ℝ) ^ 3) :
    8 * (((p.n : ℝ) * t) ^ 2 + p.n * t + (b + 1 : ℕ) * p.n * t * C) ≤ p.d := by
  let S := 1 + (p.n : ℝ) + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hH : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by
    exact div_nonneg (mul_nonneg hp.1.le (sq_nonneg _)) hp.2.2.2.1.le
  have hS : 1 ≤ S := by dsimp [S]; have := Nat.cast_nonneg (α := ℝ) p.n; linarith
  have hnS : (p.n : ℝ) ≤ S := by dsimp [S]; linarith
  have hHS : p.L0 * p.R ^ 2 / p.ε ≤ S := by
    dsimp [S]; have := Nat.cast_nonneg (α := ℝ) p.n; linarith
  have hbnd := dimension_polynomial p.n t b S C hS hnS (ht.trans hHS) hb hC hCb
  have hpow : S ^ 8 ≤ S ^ 24 := pow_le_pow_right₀ hS (by omega)
  have hcoef : (2 : ℝ) ^ 19 ≤ 2 ^ 80 := by norm_num
  have hdim : (⌈(2 : ℝ) ^ 80 * S ^ 24⌉₊ : ℝ) ≤ p.d := by
    dsimp only [S]
    exact_mod_cast hp.2.2.2.2.2.2.2
  calc
    _ ≤ 2 ^ 19 * S ^ 8 := hbnd
    _ ≤ 2 ^ 80 * S ^ 24 := mul_le_mul hcoef hpow (by positivity) (by positivity)
    _ ≤ (⌈(2 : ℝ) ^ 80 * S ^ 24⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ _ := hdim

lemma curvature_tuned (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (L R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hlen : 144 * n * (t : ℝ) ^ 2 ≤ L * R ^ 2 / ε) :
    12 * (4 * ε / t) / (R / (Real.sqrt n * t * Real.sqrt t)) ^ 2 ≤ L / 3 := by
  rw [scale_curvature n t hn ht R ε (ne_of_gt hR)]
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  have h := (le_div_iff₀ hε).mp hlen
  nlinarith only [h]

lemma gradient_tuned (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (L R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hH : 144 ≤ L * R ^ 2 / ε)
    (hlen : 144 * n * (t : ℝ) ^ 2 ≤ L * R ^ 2 / ε) :
    ((4 * ε / t) / (R / (Real.sqrt n * t * Real.sqrt t))) *
      (1 + 2 * Real.sqrt t) ≤ L * R / 12 := by
  apply (scale_gradient n t hn ht R ε hR hε.le).trans
  apply (div_le_iff₀ hR).mpr
  have h := (le_div_iff₀ hε).mp (gradient_tuning n t (L * R ^ 2 / ε) hH hlen)
  nlinarith only [h]

lemma threshold_tuned (t : ℕ) (ht : 0 < t) (L R ε : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hH : 144 ≤ L * R ^ 2 / ε) :
    4 * R + ((t : ℝ) * (4 * ε / t) / 2 + 4 * L * R ^ 2 / 9) / (L * R / 12) ≤ 10 * R := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have he : (t : ℝ) * (4 * ε / t) / 2 = 2 * ε := by field_simp; norm_num
  rw [he]
  have h := (le_div_iff₀ hε).mp hH
  have hfrac : (2 * ε + 4 * L * R ^ 2 / 9) / (L * R / 12) ≤ 6 * R := by
    apply (div_le_iff₀ (by positivity : 0 < L * R / 12)).mpr
    nlinarith only [h, hε]
  linarith only [hfrac]

lemma hiding_ratio (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (R : ℝ) (hR : R ≠ 0) :
    (10 * R) ^ 2 / ((R / (Real.sqrt n * t * Real.sqrt t)) / 16) ^ 2 =
      25600 * n * (t : ℝ) ^ 3 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  simp only [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg t)]
  field_simp
  ring

end LongTails.Proofs.InterpolatedFiniteSumSmoothParameters
