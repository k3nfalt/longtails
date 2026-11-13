import LongTails.Proofs.CountdownPath
import LongTails.Proofs.CountdownMixing
import Mathlib.Algebra.Order.Floor.Semifield

namespace OracleTemplate.CountdownMarkov

noncomputable def calibratedJump (H : ℕ) (q : ℝ) (hH : 0 < H)
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) : unitInterval := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hd : 0 < (H : ℝ) * (1 - q) := mul_pos (by exact_mod_cast hH) (by linarith)
  refine ⟨q / (H * (1 - q)), div_nonneg hq hd.le, (div_le_one hd).mpr ?_⟩
  nlinarith

lemma calibratedJump_mass (H : ℕ) (q : ℝ) (hH : 0 < H)
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    H * (calibratedJump H q hH hq hq1 : ℝ) /
      (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) = q := by
  have hHr : (H : ℝ) ≠ 0 := by positivity
  have hd : 1 - q ≠ 0 := by linarith
  change H * (q / (H * (1 - q))) / (1 + H * (q / (H * (1 - q)))) = q
  field_simp
  ring

lemma calibratedJump_entry (H : ℕ) (q : ℝ) (hH : 0 < H)
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    (calibratedJump H q hH hq hq1 : ℝ) /
      (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) = q / H := by
  have hm := calibratedJump_mass H q hH hq hq1
  have hHr : (H : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hHr).mpr
  calc
    _ = H * (calibratedJump H q hH hq hq1 : ℝ) /
        (1 + H * (calibratedJump H q hH hq hq1 : ℝ)) := by ring
    _ = q := hm

lemma sqrt_mass_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 16) :
    2 * q / (1 - q) ≤ Real.sqrt q := by
  have hs : Real.sqrt q ≤ 1 / 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have hsq := Real.sq_sqrt hq
  have hsn := Real.sqrt_nonneg q
  apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith [mul_nonneg hsn (show 0 ≤ 1 - q - 2 * Real.sqrt q by linarith)]

lemma log_inverse_half_ge_one {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 16) :
    1 ≤ Real.log (1 / q) / 2 := by
  have hl := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num)
  rw [Real.log_inv] at hl
  have htwo : 1 / 2 ≤ Real.log 2 := by norm_num at hl ⊢; linarith
  have hqinv : (16 : ℝ) ≤ 1 / q := (le_div_iff₀ hq).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hqinv
  have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  rw [he] at hlog
  linarith

lemma floor_length_bounds {q τ γ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 16)
    (hτ : 1 ≤ τ) (hγ : 0 < γ) :
    0 < ⌊τ * (Real.log (1 / q) / 2) ^ (1 / γ)⌋₊ ∧
    τ * (Real.log (1 / q) / 2) ^ (1 / γ) / 2 ≤
      (⌊τ * (Real.log (1 / q) / 2) ^ (1 / γ)⌋₊ : ℝ) := by
  have hl := log_inverse_half_ge_one hq hq1
  have hr : 1 ≤ (Real.log (1 / q) / 2) ^ (1 / γ) :=
    Real.one_le_rpow hl (by positivity)
  have hh : 1 ≤ τ * (Real.log (1 / q) / 2) ^ (1 / γ) := by nlinarith
  constructor
  · exact Nat.floor_pos.mpr hh
  · exact (Nat.div_two_lt_floor hh).le

lemma stretched_at_length {q τ γ h : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 16)
    (hτ : 0 < τ) (hγ : 0 < γ) (hh : 0 ≤ h)
    (hbound : h ≤ τ * (Real.log (1 / q) / 2) ^ (1 / γ)) :
    Real.sqrt q ≤ Real.exp (-((h / τ) ^ γ)) := by
  have hl := log_inverse_half_ge_one hq hq1
  have hb : h / τ ≤ (Real.log (1 / q) / 2) ^ (1 / γ) := (div_le_iff₀ hτ).mpr (by simpa only [mul_comm] using hbound)
  have hr := Real.rpow_le_rpow (div_nonneg hh hτ.le) hb hγ.le
  rw [← Real.rpow_mul (by linarith : 0 ≤ Real.log (1 / q) / 2),
    one_div_mul_cancel hγ.ne', Real.rpow_one] at hr
  have he : Real.sqrt q = Real.exp (-(Real.log (1 / q) / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq, one_div q, Real.log_inv]
    congr 1
    ring
  rw [he]
  exact Real.exp_le_exp.mpr (neg_le_neg hr)

lemma calibratedJump_scale (H : ℕ) (q : ℝ) (hH : 0 < H)
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    2 * H * (calibratedJump H q hH hq hq1 : ℝ) = 2 * q / (1 - q) := by
  have hHr : (H : ℝ) ≠ 0 := by positivity
  change 2 * H * (q / (H * (1 - q))) = 2 * q / (1 - q)
  field_simp

lemma calibrated_mixing (H : ℕ) (q : ℝ) (hH : 0 < H)
    (hq : 0 < q) (hq1 : q ≤ 1 / 16) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hbound : (H : ℝ) ≤ τ * (Real.log (1 / q) / 2) ^ (1 / γ)) (n : ℕ) :
    (∫ x, LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.mixingDistance
      (kernel H (calibratedJump H q hH hq.le (by linarith)))
      (stationaryLaw H (calibratedJump H q hH hq.le (by linarith))) n x
      ∂stationaryMeasure H (calibratedJump H q hH hq.le (by linarith))) ≤
      Real.exp (-(((n : ℝ) / τ) ^ γ)) := by
  apply average_mixing_stretched H hH _ hτ hγ hγ1 _ n
  rw [calibratedJump_scale]
  exact (sqrt_mass_bound hq.le hq1).trans
    (stretched_at_length hq hq1 hτ hγ (Nat.cast_nonneg H) hbound)

open MeasureTheory

lemma calibrated_commonPrefix_lower (H : ℕ) (q : ℝ) (hH : 0 < H)
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) (n : ℕ) :
    1 - q - n * q / H ≤
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (kernel H (calibratedJump H q hH hq hq1))
      (stationaryLaw H (calibratedJump H q hH hq hq1)) : Measure (ℕ → ℝ)).real
      (commonPrefix 0 n) := by
  have h := commonPrefix_lower H hH (calibratedJump H q hH hq hq1) n
  rw [calibratedJump_mass, mul_div_assoc, calibratedJump_entry, ← mul_div_assoc] at h
  exact h

lemma floor_budget_entry_bound {q C : ℝ} (hq : 0 < q) (hC : 1 ≤ C)
    {n : ℕ} (hn : n ≤ ⌊C / (32 * q)⌋₊) :
    (n : ℝ) * q / (⌊C⌋₊ : ℝ) ≤ 1 / 16 := by
  have hfloor : (0 : ℝ) < ⌊C⌋₊ := by exact_mod_cast (Nat.floor_pos.mpr hC)
  have hhalf := Nat.div_two_lt_floor hC
  have hnreal : (n : ℝ) ≤ C / (32 * q) :=
    (Nat.cast_le.mpr hn).trans (Nat.floor_le (by positivity))
  have hnq := (le_div_iff₀ (by positivity : 0 < 32 * q)).mp hnreal
  apply (div_le_iff₀ hfloor).mpr
  nlinarith

lemma calibrated_commonPrefix_seven_eighths {q C : ℝ} (hq : 0 < q)
    (hq1 : q ≤ 1 / 16) (hC : 1 ≤ C) {n : ℕ} (hn : n ≤ ⌊C / (32 * q)⌋₊) :
    7 / 8 ≤ (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (kernel ⌊C⌋₊ (calibratedJump ⌊C⌋₊ q (Nat.floor_pos.mpr hC) hq.le (by linarith)))
      (stationaryLaw ⌊C⌋₊ (calibratedJump ⌊C⌋₊ q (Nat.floor_pos.mpr hC) hq.le (by linarith))) :
      Measure (ℕ → ℝ)).real (commonPrefix 0 n) := by
  have h := calibrated_commonPrefix_lower ⌊C⌋₊ q (Nat.floor_pos.mpr hC) hq.le
    (by linarith : q ≤ 1 / 2) n
  have hb := floor_budget_entry_bound hq hC hn
  linarith

end OracleTemplate.CountdownMarkov
