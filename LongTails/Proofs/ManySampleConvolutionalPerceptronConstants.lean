import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronConstants

lemma drift_small {δ U M : ℝ} (hδ : 0 ≤ δ) (hU : 0 ≤ U)
    (hM : M ≤ 4097 * U ^ 2) (hsmall : δ * U ^ 3 ≤ 1 / 16777216) :
    δ * M * (256 * U) < 1 / 2 := by
  have hmul := mul_le_mul_of_nonneg_left hM (mul_nonneg hδ hU)
  nlinarith

lemma height_small {U B m : ℝ} (hU : 0 < U) (hB : 0 ≤ B)
    (hBU : B ≤ U) (hm : m ≤ 4097 * U ^ 2) :
    16 * B ^ 2 + 4 * m < (256 * U) ^ 2 := by
  have hsq : B ^ 2 ≤ U ^ 2 := by nlinarith
  nlinarith [sq_pos_of_pos hU]

lemma noise_floor {δ U ρ : ℝ} (hδ : 0 ≤ δ) (hU : 1 ≤ U)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : δ * U ^ 2 ≤ ρ ^ 4 / 16777216) :
    δ * (256 * U + 1) / ρ ^ 2 ≤ 257 / 16777216 := by
  have hU' : 0 ≤ U := by linarith
  have hsq : U ≤ U ^ 2 := by nlinarith
  have hδU := mul_le_mul_of_nonneg_left hsq hδ
  have hδ1 := mul_le_mul_of_nonneg_left hU hδ
  have hnum : δ * (256 * U + 1) ≤ 257 * (δ * U ^ 2) := by nlinarith
  have hr2 : ρ ^ 2 ≤ 1 := by nlinarith
  have hr4 : ρ ^ 4 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (ρ ^ 2)]
  apply (div_le_iff₀ (sq_pos_of_pos hρ)).mpr
  nlinarith

lemma norm_increment_small {δ U ρ κ : ℝ} (hδ : 0 ≤ δ) (hU : 1 ≤ U)
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : δ * U ^ 2 ≤ ρ ^ 4 / 16777216) :
    64 * δ * (256 * U + 1) ^ 2 / ρ ^ 4 + (κ / 4 + 3 / 2) ^ 2 < 4 := by
  have hU' : 0 ≤ U := by linarith
  have hsq : (256 * U + 1) ^ 2 ≤ 257 ^ 2 * U ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hδ
  have hnum : 64 * δ * (256 * U + 1) ^ 2 / ρ ^ 4 ≤
      64 * 257 ^ 2 / 16777216 := by
    apply (div_le_iff₀ (pow_pos hρ 4)).mpr
    nlinarith
  nlinarith

lemma terminal_contradiction {U B m κ y R : ℝ} (hU : 0 < U) (hB : 0 ≤ B)
    (hBU : B ≤ U) (hκ : 0 ≤ κ) (hκU : 1 ≤ κ * U)
    (hm : 4095 * U ^ 2 ≤ m) (hm' : m ≤ 4097 * U ^ 2)
    (hy : -4 * B + κ * m / 4 ≤ y) (hyR : y ≤ R)
    (hR : R ^ 2 ≤ 16 * B ^ 2 + 4 * m) : False := by
  have hmul := mul_le_mul_of_nonneg_left hm hκ
  have hU2 := mul_le_mul_of_nonneg_right hκU hU.le
  have hy' : 1000 * U ≤ R := by nlinarith
  have hs : (1000 * U) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (by positivity) (by nlinarith)).mpr hy'
  have hB2 : B ^ 2 ≤ U ^ 2 := by nlinarith
  nlinarith [sq_pos_of_pos hU]

lemma burnin_half (X : ℝ) : X / 2 ≤ (((⌈X⌉₊ + 2) / 2 : ℕ) : ℝ) := by
  have hn : ⌈X⌉₊ ≤ 2 * ((⌈X⌉₊ + 2) / 2) := by omega
  have hr : (⌈X⌉₊ : ℝ) ≤ 2 * (((⌈X⌉₊ + 2) / 2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hx := Nat.le_ceil X
  linarith

lemma burnin_decay {ρ δ : ℝ} {m : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hm : 4 / ρ ^ 2 * Real.log (1 / δ) ≤ m) :
    (1 - ρ ^ 2 / 2) ^ m ≤ δ ^ 2 := by
  have hr : 0 ≤ 1 - ρ ^ 2 / 2 := by nlinarith
  have hp := pow_le_pow_left₀ hr (Real.one_sub_le_exp_neg (ρ ^ 2 / 2)) m
  rw [← Real.exp_nat_mul] at hp
  have hmul := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ ρ ^ 2 / 2)
  have hid : (4 / ρ ^ 2 * Real.log (1 / δ)) * (ρ ^ 2 / 2) =
      2 * Real.log (1 / δ) := by field_simp [ne_of_gt hρ]; ring
  rw [hid] at hmul
  have hlog : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [hlog] at hmul
  have he : (m : ℝ) * -(ρ ^ 2 / 2) ≤ 2 * Real.log δ := by nlinarith
  calc
    _ ≤ Real.exp ((m : ℝ) * -(ρ ^ 2 / 2)) := hp
    _ ≤ Real.exp (2 * Real.log δ) := Real.exp_le_exp.mpr he
    _ = δ ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hδ]

lemma nuisance_small {δ U ρ κ : ℝ} (hδ : 0 ≤ δ) (hU : 1 ≤ U)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 ≤ κ) (hκU : 1 ≤ κ * U)
    (hsmall : δ * U ^ 2 ≤ ρ ^ 4 / 16777216) :
    8 * δ * (256 * U + 1) / ρ ^ 2 ≤ κ / 4 := by
  have hU' : 0 ≤ U := by linarith
  have hm := mul_le_mul_of_nonneg_left hsmall hκ
  have hi := mul_le_mul_of_nonneg_left hκU (mul_nonneg hδ hU')
  have hsq : ρ ^ 2 ≤ 1 := by nlinarith
  have hp : ρ ^ 4 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (ρ ^ 2)]
  have hpκ := mul_le_mul_of_nonneg_left hp hκ
  have hδU := mul_le_mul_of_nonneg_left hU hδ
  apply (div_le_iff₀ (sq_pos_of_pos hρ)).mpr
  nlinarith

lemma global_mass_threshold {δ U ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hU : 1 ≤ U) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : δ * U ^ 2 ≤ ρ ^ 4 / 16777216) :
    3 + 12 * (δ * (256 * U) + δ ^ 2) / ρ ^ 2 ≤ 4 := by
  have hf := noise_floor hδ hU hρ hρ1 hsmall
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hquot : (δ * (256 * U) + δ ^ 2) / ρ ^ 2 ≤ δ * (256 * U + 1) / ρ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg ρ)
    nlinarith
  have hid : 12 * (δ * (256 * U) + δ ^ 2) / ρ ^ 2 =
      12 * ((δ * (256 * U) + δ ^ 2) / ρ ^ 2) := by ring
  rw [hid]
  linarith

lemma post_mass_threshold {δ H ρ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hH : 0 ≤ H) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    3 * δ ^ 2 + 12 * (δ * H + δ ^ 2) / ρ ^ 2 ≤
      2 * (8 * δ * (H + 1) / ρ ^ 2) := by
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hr2 : ρ ^ 2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hr2 (sq_nonneg δ)
  have hprod := mul_nonneg hδ hH
  have hcancel : (12 * (δ * H + δ ^ 2) / ρ ^ 2) * ρ ^ 2 = 12 * (δ * H + δ ^ 2) :=
    div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hρ))
  have hcancel' : (8 * δ * (H + 1) / ρ ^ 2) * ρ ^ 2 = 8 * δ * (H + 1) :=
    div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hρ))
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hρ)).mp
  nlinarith

lemma escape_amplification {ρ σ : ℝ} {m : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσ : 0 < σ) (hm : 2 / ρ * Real.log (8 / σ) ≤ m) :
    8 ≤ σ * (1 + ρ) ^ m := by
  have hlog0 := Real.le_log_one_add_of_nonneg hρ.le
  have hlog : ρ / 2 ≤ Real.log (1 + ρ) := by
    have hrat : ρ / 2 ≤ 2 * ρ / (ρ + 2) := by
      apply (le_div_iff₀ (by linarith : 0 < ρ + 2)).mpr
      nlinarith
    exact hrat.trans hlog0
  have hmul := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ ρ / 2)
  have hid : (2 / ρ * Real.log (8 / σ)) * (ρ / 2) = Real.log (8 / σ) := by
    field_simp [ne_of_gt hρ]
  rw [hid] at hmul
  have hmlog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hexp := Real.exp_le_exp.mpr (hmul.trans hmlog)
  rw [Real.exp_log (by positivity : 0 < 8 / σ), Real.exp_nat_mul,
    Real.exp_log (by linarith : 0 < 1 + ρ)] at hexp
  simpa only [mul_comm] using (div_le_iff₀ hσ).mp hexp

end LongTails.Proofs.ManySampleConvolutionalPerceptronConstants
