import LongTails.Proofs.InterpolatedFiniteSumSmoothParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Proofs.InterpolatedFiniteSumExponentialParameters

lemma gradient_tuned (t : ℕ) (ht : 0 < t) (η L : ℝ) (hη : 0 < η) (hL : 0 < L) :
    ((2 * η / t) / (84 * η / (L * Real.sqrt t))) * (1 + 2 * Real.sqrt t) ≤ L / 14 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs1 : 1 ≤ Real.sqrt t := by
    have hh := Real.sqrt_le_sqrt ht1
    simpa using hh
  have hsq := Real.sq_sqrt ht0.le
  have he : ((2 * η / t) / (84 * η / (L * Real.sqrt t))) * (1 + 2 * Real.sqrt t) =
      L * (1 + 2 * Real.sqrt t) / (42 * Real.sqrt t) := by
    field_simp
    nlinarith only [hsq]
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 42 * Real.sqrt t)).mpr
  have hh := mul_le_mul_of_nonneg_left hs1 hL.le
  nlinarith only [hh]

lemma curvature_tuned (t : ℕ) (ht : 0 < t) (η L : ℝ) (hη : 1 / 8 ≤ η) (hL : 0 < L) :
    12 * (2 * η / t) / (84 * η / (L * Real.sqrt t)) ^ 2 ≤ (4 * L ^ 2 / 49) / 3 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hη0 : 0 < η := by linarith
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq := Real.sq_sqrt ht0.le
  have he : 12 * (2 * η / t) / (84 * η / (L * Real.sqrt t)) ^ 2 = L ^ 2 / (294 * η) := by
    field_simp
    nlinarith only [hsq]
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 294 * η)).mpr
  have hh := mul_le_mul_of_nonneg_left hη (sq_nonneg L)
  nlinarith only [hh]

lemma radius_tuned (g t : ℕ) (ht : 0 < t) (η L R : ℝ) (hL : 0 < L)
    (hscale : (g : ℝ) * (84 * η) ^ 2 * (t : ℝ) ^ 2 ≤ (L * R) ^ 2) :
    (g : ℝ) * (t : ℝ) ^ 3 * (84 * η / (L * Real.sqrt t)) ^ 2 ≤ R ^ 2 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq := Real.sq_sqrt ht0.le
  have he : (g : ℝ) * (t : ℝ) ^ 3 * (84 * η / (L * Real.sqrt t)) ^ 2 =
      ((g : ℝ) * (84 * η) ^ 2 * (t : ℝ) ^ 2) / L ^ 2 := by
    field_simp
    rw [hsq]
    ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith only [hscale]

lemma radial_tuned (L R : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (hq : 21 / 2 ≤ L * R) :
    4 * (L / 14) / R ≤ (4 * L ^ 2 / 49) / 3 := by
  apply (div_le_iff₀ hR).mpr
  have hh := mul_le_mul_of_nonneg_left hq hL
  nlinarith only [hh]

lemma exponential_scale (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    δ * Real.exp (Real.log (1 + 2 * ε / δ)) = δ + 2 * ε := by
  rw [Real.exp_log (by positivity : 0 < 1 + 2 * ε / δ)]
  field_simp

lemma eta_lower (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hδε : δ ≤ ε / 4) :
    1 / 8 ≤ Real.log (1 + 2 * ε / δ) := by
  have hx : (9 : ℝ) ≤ 1 + 2 * ε / δ := by
    have hh : 8 ≤ 2 * ε / δ := (le_div_iff₀ hδ).mpr (by linarith)
    linarith
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < (1 + 2 * ε / δ)⁻¹)
  rw [Real.log_inv] at hl
  have hi : (1 + 2 * ε / δ)⁻¹ ≤ (1 : ℝ) / 9 := by
    simpa only [one_div] using (inv_le_inv₀ (by linarith : 0 < 1 + 2 * ε / δ) (by norm_num : (0 : ℝ) < 9)).mpr hx
  linarith

lemma length_bounds (g : ℕ) (hg : 0 < g) (q η : ℝ) (hη : 0 < η)
    (hregime : 84 * η * Real.sqrt g ≤ q) :
    0 < ⌊q / (84 * η * Real.sqrt g)⌋₊ ∧
    (g : ℝ) * (84 * η) ^ 2 * (⌊q / (84 * η * Real.sqrt g)⌋₊ : ℝ) ^ 2 ≤ q ^ 2 ∧
    q / (168 * η * Real.sqrt g) ≤ (⌊q / (84 * η * Real.sqrt g)⌋₊ : ℝ) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hden : 0 < 84 * η * Real.sqrt g := by positivity
  have hx : 1 ≤ q / (84 * η * Real.sqrt g) := (le_div_iff₀ hden).mpr (by simpa using hregime)
  have ht := Nat.floor_pos.mpr hx
  have hq : 0 < q := hden.trans_le hregime
  have hf := Nat.floor_le (by positivity : 0 ≤ q / (84 * η * Real.sqrt g))
  have hupper := Nat.lt_floor_add_one (q / (84 * η * Real.sqrt g))
  have ht1 : (1 : ℝ) ≤ (⌊q / (84 * η * Real.sqrt g)⌋₊ : ℝ) := by exact_mod_cast ht
  refine ⟨ht, ?_, ?_⟩
  · have hh := (le_div_iff₀ hden).mp hf
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (⌊q / (84 * η * Real.sqrt g)⌋₊ : ℝ) *
      (84 * η * Real.sqrt g)) hh 2
    have hsq := Real.sq_sqrt hgR.le
    simp only [mul_pow, hsq] at hs
    nlinarith only [hs]
  · have he : q / (168 * η * Real.sqrt g) = (q / (84 * η * Real.sqrt g)) / 2 := by ring
    rw [he]
    linarith only [hupper, ht1]

lemma hiding_ratio (t : ℕ) (ht : 0 < t) (η L R : ℝ) (hη : 0 < η) (hL : 0 < L) :
    (10 * R) ^ 2 / ((84 * η / (L * Real.sqrt t)) / (64 * η)) ^ 2 ≤
      100 * (L * R) ^ 2 * t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq := Real.sq_sqrt ht0.le
  have he : (10 * R) ^ 2 / ((84 * η / (L * Real.sqrt t)) / (64 * η)) ^ 2 =
      (25600 / 441 : ℝ) * (L * R) ^ 2 * t := by
    field_simp
    rw [hsq]
    ring
  rw [he]
  have hh : 0 ≤ (L * R) ^ 2 * t := by positivity
  nlinarith only [hh]

lemma dimension_polynomial (g t b : ℕ) (S C : ℝ) (hS : 1 ≤ S)
    (hg : (g : ℝ) ≤ S) (ht : (t : ℝ) ≤ S) (hb : b + 1 ≤ 2 * g * t)
    (hC : 0 ≤ C) (hCb : C ≤ 25600 * S ^ 4) :
    8 * (((g : ℝ) * t) ^ 2 + g * t + (b + 1 : ℕ) * g * t * C) ≤ 2 ^ 19 * S ^ 8 := by
  have hS0 : 0 ≤ S := by linarith
  have hs2 : S ^ 2 ≤ S ^ 8 := pow_le_pow_right₀ hS (by omega)
  have hs4 : S ^ 4 ≤ S ^ 8 := pow_le_pow_right₀ hS (by omega)
  have hgt : (g : ℝ) * t ≤ S ^ 8 := by
    calc
      _ ≤ S * S := mul_le_mul hg ht (Nat.cast_nonneg t) hS0
      _ = S ^ 2 := by ring
      _ ≤ _ := hs2
  have hgt2 : ((g : ℝ) * t) ^ 2 ≤ S ^ 8 := by
    calc
      _ ≤ (S * S) ^ 2 := by gcongr
      _ = S ^ 4 := by ring
      _ ≤ _ := hs4
  have hbR : ((b + 1 : ℕ) : ℝ) ≤ 2 * g * t := by exact_mod_cast hb
  have hlast : ((b + 1 : ℕ) : ℝ) * g * t * C ≤ 51200 * S ^ 8 := by
    calc
      _ ≤ (2 * g * t) * g * t * (25600 * S ^ 4) := by gcongr
      _ = 51200 * (g : ℝ) ^ 2 * (t : ℝ) ^ 2 * S ^ 4 := by ring
      _ ≤ 51200 * S ^ 2 * S ^ 2 * S ^ 4 := by gcongr
      _ = _ := by ring
  have hp : 0 ≤ S ^ 8 := by positivity
  norm_num only [show (2 : ℝ) ^ 19 = 524288 by norm_num]
  nlinarith only [hgt, hgt2, hlast, hp]

lemma setup_dimension
    (p : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Params)
    (hp : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.valid p)
    (g t b : ℕ) (hg : g ≤ p.n) (ht : (t : ℝ) ≤ p.L1 * p.R) (hb : b + 1 ≤ 2 * g * t)
    (C : ℝ) (hC : 0 ≤ C) (hCb : C ≤ 100 * (p.L1 * p.R) ^ 2 * t) :
    8 * (((g : ℝ) * t) ^ 2 + g * t + (b + 1 : ℕ) * g * t * C) ≤ p.d := by
  let S := 1 + (p.n : ℝ) + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hH : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by
    exact div_nonneg (mul_nonneg hp.1.le (sq_nonneg _)) hp.2.2.2.1.le
  have hS : 1 ≤ S := by dsimp [S]; have := Nat.cast_nonneg (α := ℝ) p.n; linarith
  have hnS : (p.n : ℝ) ≤ S := by dsimp [S]; linarith
  have hqS : p.L1 * p.R ≤ S := by dsimp [S]; have := Nat.cast_nonneg (α := ℝ) p.n; linarith
  have hgS : (g : ℝ) ≤ S := (by exact_mod_cast hg : (g : ℝ) ≤ p.n).trans hnS
  have hCS : C ≤ 25600 * S ^ 4 := by
    calc
      C ≤ 100 * (p.L1 * p.R) ^ 2 * t := hCb
      _ ≤ 100 * S ^ 2 * S := by gcongr; exact ht.trans hqS
      _ = 100 * S ^ 3 := by ring
      _ ≤ 25600 * S ^ 4 := mul_le_mul (by norm_num) (pow_le_pow_right₀ hS (by omega))
        (by positivity) (by positivity)
  have hbnd := dimension_polynomial g t b S C hS hgS (ht.trans hqS) hb hC hCS
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

end LongTails.Proofs.InterpolatedFiniteSumExponentialParameters
