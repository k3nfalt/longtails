import LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension
import Mathlib.Tactic

namespace LongTails.Proofs.AdaptiveTransientParameters

open LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension

noncomputable def degree (p : Params) : ℕ := ⌈16 * Real.sqrt (p.L1 * p.R)⌉₊

noncomputable def width (p : Params) : ℝ := 131072 * p.R

lemma sqrt_one_le (q : ℝ) (hq : 1 ≤ q) : 1 ≤ Real.sqrt q := by
  have hs := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hn := Real.sqrt_nonneg q
  nlinarith

lemma degree_ge_two (q : ℝ) (hq : 1 ≤ q) : 2 ≤ ⌈16 * Real.sqrt q⌉₊ := by
  have hs := sqrt_one_le q hq
  have hh := Nat.le_ceil (16 * Real.sqrt q)
  have ht : (2 : ℝ) ≤ (⌈16 * Real.sqrt q⌉₊ : ℝ) := by linarith
  exact_mod_cast ht

lemma degree_product (q : ℝ) (hq : 1 ≤ q) :
    (⌈16 * Real.sqrt q⌉₊ : ℝ) * ((⌈16 * Real.sqrt q⌉₊ + 1 : ℕ) : ℝ) ≤ 306 * q := by
  have hs := sqrt_one_le q hq
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.sqrt q by positivity)
  have h1 : (⌈16 * Real.sqrt q⌉₊ : ℝ) ≤ 17 * Real.sqrt q := by linarith
  have h2 : ((⌈16 * Real.sqrt q⌉₊ + 1 : ℕ) : ℝ) ≤ 18 * Real.sqrt q := by
    push_cast
    linarith
  have hm := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ (⌈16 * Real.sqrt q⌉₊ + 1 : ℕ))
    (by positivity : 0 ≤ 17 * Real.sqrt q)
  have he := Real.sq_sqrt (show 0 ≤ q by linarith)
  nlinarith only [hm, he]

lemma exponential_suppression (q : ℝ) (hq : 1 ≤ q) :
    q ^ 2 * Real.exp (Real.sqrt q) ≤ (2 : ℝ) ^ ⌈16 * Real.sqrt q⌉₊ := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hs := Real.log_le_sub_one_of_pos hs0
  rw [Real.log_sqrt hq0.le] at hs
  have hlog : Real.log q ≤ 2 * Real.sqrt q := by linarith
  have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num [Real.log_div] at ht
  have hhalf : 1 / 2 ≤ Real.log 2 := by linarith
  have hn := Nat.le_ceil (16 * Real.sqrt q)
  have hm := mul_le_mul_of_nonneg_left hhalf
    (show 0 ≤ (⌈16 * Real.sqrt q⌉₊ : ℝ) by positivity)
  have he : 2 * Real.log q + Real.sqrt q ≤ (⌈16 * Real.sqrt q⌉₊ : ℝ) * Real.log 2 := by
    nlinarith only [hlog, hn, hm, Real.sqrt_nonneg q]
  have hh := Real.exp_le_exp.mpr he
  have hqexp : Real.exp (2 * Real.log q) = q ^ 2 := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.exp_log (sq_pos_of_pos hq0)
  have h2exp : Real.exp ((⌈16 * Real.sqrt q⌉₊ : ℝ) * Real.log 2) = 2 ^ ⌈16 * Real.sqrt q⌉₊ := by
    simpa only [Real.log_pow] using Real.exp_log
      (by positivity : (0 : ℝ) < 2 ^ ⌈16 * Real.sqrt q⌉₊)
  rw [Real.exp_add, hqexp, h2exp] at hh
  exact hh

lemma peak_suppression (m : ℕ) (hm : 0 < m) (L₀ L₁ R ε : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hR : 0 < R)
    (hup : ε ≤ L₀ * R ^ 2 / 16) (hmq : (m : ℝ) ≤ L₁ * R) (hq : 1 ≤ L₁ * R) :
    (ε * L₁ / 2 * Real.exp (((m : ℝ) - 1) / Real.sqrt m)) *
      (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (L₁ * R)⌉₊ * L₁ ≤ L₀ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : ((m : ℝ) - 1) / Real.sqrt m ≤ Real.sqrt (L₁ * R) := by
    apply le_trans _ (Real.sqrt_le_sqrt hmq)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hm0)).mpr
    nlinarith [Real.sq_sqrt hm0.le]
  have he := Real.exp_le_exp.mpr hs
  have hcoef : ε * L₁ ^ 2 / 2 ≤ L₀ * (L₁ * R) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hup (sq_nonneg L₁)
    have hz : 0 ≤ L₀ * R ^ 2 * L₁ ^ 2 := by positivity
    nlinarith only [hh, hz]
  have hm1 := mul_le_mul hcoef he (Real.exp_pos _).le (by positivity : 0 ≤ L₀ * (L₁ * R) ^ 2)
  have hm2 := mul_le_mul_of_nonneg_left (exponential_suppression (L₁ * R) hq) h0.le
  have ht : (ε * L₁ / 2 * Real.exp (((m : ℝ) - 1) / Real.sqrt m)) * L₁ ≤
      L₀ * (2 : ℝ) ^ ⌈16 * Real.sqrt (L₁ * R)⌉₊ := by nlinarith only [hm1, hm2]
  have hd := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ ⌈16 * Real.sqrt (L₁ * R)⌉₊)).mpr ht
  rw [div_pow, one_pow]
  simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hd

lemma hiding_ratio (m : ℕ) (hm : 0 < m) (L₁ R : ℝ) (h1 : 0 < L₁) :
    (524288 * R) ^ 2 / (1 / (4 * L₁ * Real.sqrt m)) ^ 2 =
      4398046511104 * (L₁ * R) ^ 2 * (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := Real.sq_sqrt hm0.le
  have hsn := (Real.sqrt_pos.mpr hm0).ne'
  have hL := h1.ne'
  field_simp
  nlinarith only [hs]

lemma hiding_dimension (m : ℕ) (q : ℝ) (hq : 1 ≤ q) (hmq : (m : ℝ) ≤ q) :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * (4398046511104 * q ^ 2 * (m : ℝ)) ≤
      17592186044416 * (1 + q) ^ 5 := by
  have hm3 := pow_le_pow_left₀ (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hmq 3
  have hmul := mul_le_mul_of_nonneg_left hm3 (show 0 ≤ 8796093022208 * q ^ 2 by positivity)
  have hq1 : q ≤ (1 + q) ^ 5 := by
    calc
      q ≤ 1 + q := by linarith
      _ ≤ (1 + q) ^ 5 := by
        simpa using pow_le_pow_right₀ (show 1 ≤ 1 + q by linarith) (show 1 ≤ 5 by norm_num)
  have hq5 : q ^ 5 ≤ (1 + q) ^ 5 := by
    exact pow_le_pow_left₀ (by linarith) (by linarith) 5
  have hpos : 0 ≤ (1 + q) ^ 5 := by positivity
  nlinarith only [hmq, hmul, hq1, hq5, hpos]

end LongTails.Proofs.AdaptiveTransientParameters
