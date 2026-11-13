import LongTails.Proofs.GeneralizedSmoothHardChainRadius

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GeneralizedSmoothTransientDimension

open GeneralizedSmoothHardChain

lemma peak_radius_bound (m : ℕ) (hm : 0 < m) (L₀ L₁ R ε : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hR : 0 < R) (hε : 0 < ε)
    (hup : ε ≤ L₀ * R ^ 2 / 16) (hmq : (m : ℝ) ≤ L₁ * R) :
    peak m (L₁ / 4) ε / (L₀ / 32) ≤ R * (L₁ * R) * Real.exp (Real.sqrt (L₁ * R)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : ((m : ℝ) - 1) / Real.sqrt m ≤ Real.sqrt (L₁ * R) := by
    apply le_trans _ (Real.sqrt_le_sqrt hmq)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hm0)).mpr
    nlinarith [Real.sq_sqrt hm0.le]
  have he := Real.exp_le_exp.mpr hs
  have hh := mul_le_mul hup he (Real.exp_pos _).le (by positivity : 0 ≤ L₀ * R ^ 2 / 16)
  have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16 * L₁ / L₀ by positivity)
  unfold peak
  convert ht using 1 <;> field_simp
  all_goals ring

lemma exterior_radius_bound (m : ℕ) (hm : 0 < m) (L₀ L₁ R ε : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hR : 0 < R) (hε : 0 < ε)
    (hup : ε ≤ L₀ * R ^ 2 / 16) (hmq : (m : ℝ) ≤ L₁ * R) (hq : 1 ≤ L₁ * R) :
    24 * (peak m (L₁ / 4) ε + (L₀ / 32) * (R / 2)) / (L₀ / 32) ≤
      36 * R * (L₁ * R) * Real.exp (Real.sqrt (L₁ * R)) := by
  have hh := peak_radius_bound m hm L₀ L₁ R ε h0 h1 hR hε hup hmq
  have he : 1 ≤ Real.exp (Real.sqrt (L₁ * R)) := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)
  have ht : R ≤ R * (L₁ * R) * Real.exp (Real.sqrt (L₁ * R)) := by
    nlinarith [mul_le_mul hq he (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ L₁ * R)]
  have hid : 24 * (peak m (L₁ / 4) ε + (L₀ / 32) * (R / 2)) / (L₀ / 32) =
      24 * (peak m (L₁ / 4) ε / (L₀ / 32)) + 12 * R := by field_simp; ring
  rw [hid]
  linarith

lemma ratio_bound (m : ℕ) (hm : 0 < m) (q R U : ℝ) (hq : 0 < q) (hR : 0 < R)
    (hU : 0 ≤ U) (hUb : U ≤ 36 * R * q * Real.exp (Real.sqrt q)) :
    U ^ 2 / (R / (4 * q * Real.sqrt m)) ^ 2 ≤ 20736 * q ^ 4 * m * Real.exp (2 * Real.sqrt q) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := pow_le_pow_left₀ hU hUb 2
  have hθ : 0 < (R / (4 * q * Real.sqrt m)) ^ 2 := by positivity
  apply (div_le_iff₀ hθ).mpr
  convert hs using 1
  have he : Real.exp (2 * Real.sqrt q) = Real.exp (Real.sqrt q) ^ 2 := by
    rw [two_mul, Real.exp_add]
    ring
  rw [he]
  field_simp
  nlinarith [Real.sq_sqrt hm0.le]

lemma dimension_scalar (m : ℕ) (q A : ℝ) (hq : 1 ≤ q) (hmq : (m : ℝ) ≤ q)
    (hA : A ≤ 20736 * q ^ 4 * m * Real.exp (2 * Real.sqrt q)) :
    (m : ℝ) + 2 * m ^ 2 * A ≤ 1048576 * (1 + q) ^ 8 * Real.exp (2 * Real.sqrt q) := by
  have hq0 : 0 ≤ q := by linarith
  have he : 1 ≤ Real.exp (2 * Real.sqrt q) := Real.one_le_exp_iff.mpr (by positivity)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm3 := pow_le_pow_left₀ hm0 hmq 3
  have ha := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2 * (m : ℝ) ^ 2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hm3 (show 0 ≤ 41472 * q ^ 4 * Real.exp (2 * Real.sqrt q) by positivity)
  have hbase : 1 ≤ 1 + q := by linarith
  have hp7 : q ^ 7 ≤ (1 + q) ^ 8 := (pow_le_pow_left₀ hq0 (by linarith : q ≤ 1 + q) 7).trans
    (pow_le_pow_right₀ hbase (by norm_num : 7 ≤ 8))
  have hp1 : q ≤ (1 + q) ^ 8 := (show q ≤ 1 + q by linarith).trans (le_self_pow₀ hbase (by norm_num))
  have he0 : 0 ≤ Real.exp (2 * Real.sqrt q) := (Real.exp_pos _).le
  have hp7e := mul_le_mul_of_nonneg_right hp7 he0
  have hp1e := mul_le_mul hp1 he (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (1 + q) ^ 8)
  have hbig : 0 ≤ (1 + q) ^ 8 * Real.exp (2 * Real.sqrt q) := by positivity
  nlinarith only [ha, hb, hmq, hp7e, hp1e, hbig]

end LongTails.Proofs.GeneralizedSmoothTransientDimension
