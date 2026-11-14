import LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace LongTails.Proofs.GeneralizedSmoothTransientParameters

open LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension

lemma valid_original (p : Params) (hp : spec.valid p) :
    LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex.spec.valid p.toRadiusOnly :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

lemma log_upper_linear (q : ℝ) (hq : 1048576 ≤ q) :
    Real.log (2 + q) ≤ q / 32768 := by
  have hx : 0 < 2 + q := by linarith
  have hc : Real.log (1048578 : ℝ) ≤ 21 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1048578)
      (by norm_num : (1048578 : ℝ) ≤ 2 ^ 21)
    rw [Real.log_pow] at h
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h htwo
    linarith
  have ht := Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 1048578))
  rw [Real.log_div hx.ne' (by norm_num : (1048578 : ℝ) ≠ 0)] at ht
  nlinarith

lemma log_pos (q : ℝ) (hq : 1048576 ≤ q) : 0 < Real.log (2 + q) :=
  Real.log_pos (by linarith)

lemma links_bound (q : ℝ) (hq : 1048576 ≤ q) :
    ((⌊q / (4096 * Real.log (2 + q))⌋₊ + 1 : ℕ) : ℝ) ≤
      q / (2048 * Real.log (2 + q)) := by
  have hl := log_pos q hq
  have hu := log_upper_linear q hq
  have hx : 8 ≤ q / (4096 * Real.log (2 + q)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hf := Nat.floor_le (show 0 ≤ q / (4096 * Real.log (2 + q)) by positivity)
  push_cast
  have he : q / (2048 * Real.log (2 + q)) = 2 * (q / (4096 * Real.log (2 + q))) := by ring
  rw [he]
  linarith

lemma log_one_le (q : ℝ) (hq : 1048576 ≤ q) : 1 ≤ Real.log (2 + q) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ 2 + q)
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he] at hh
  have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num [Real.log_div] at ht
  linarith

lemma links_log_bound (q : ℝ) (hq : 1048576 ≤ q) :
    ((⌊q / (4096 * Real.log (2 + q))⌋₊ + 1 : ℕ) : ℝ) * Real.log (2 + q) ≤ q / 2048 := by
  have hl := log_pos q hq
  have hh := (le_div_iff₀ (show 0 < 2048 * Real.log (2 + q) by positivity)).mp (links_bound q hq)
  linarith

lemma links_le_q (q : ℝ) (hq : 1048576 ≤ q) :
    ((⌊q / (4096 * Real.log (2 + q))⌋₊ + 1 : ℕ) : ℝ) ≤ q := by
  have hm := links_log_bound q hq
  have hl := log_one_le q hq
  have hn : 0 ≤ ((⌊q / (4096 * Real.log (2 + q))⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hl)]

lemma sqrt_links_log_bound (m : ℕ) (q : ℝ) (hq : 1048576 ≤ q) (hm : (m : ℝ) ≤ q) :
    Real.log (1 + Real.sqrt m) ≤ Real.log (2 + q) := by
  apply Real.log_le_log (by positivity)
  have hs := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hn := Real.sqrt_nonneg (m : ℝ)
  nlinarith

lemma scaled_accuracy_log_bound (L₀ L₁ R ε : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (hR : 0 < R) (hε : 0 < ε) (hup : ε ≤ L₀ * R ^ 2 / 16) :
    Real.log (1 + 2 * ε * (L₁ / 4) ^ 2 / (L₀ / 4)) ≤ 2 * Real.log (2 + L₁ * R) := by
  have he : 2 * ε * (L₁ / 4) ^ 2 / (L₀ / 4) = ε * L₁ ^ 2 / (2 * L₀) := by field_simp; ring
  have hm := mul_le_mul_of_nonneg_right hup (sq_nonneg L₁)
  have hb : ε * L₁ ^ 2 / (2 * L₀) ≤ (L₁ * R) ^ 2 / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * L₀)).mpr
    nlinarith only [hm]
  have hh : 1 + 2 * ε * (L₁ / 4) ^ 2 / (L₀ / 4) ≤ (2 + L₁ * R) ^ 2 := by
    rw [he]
    nlinarith [mul_pos hL₁ hR, sq_nonneg (L₁ * R)]
  have hl := Real.log_le_log (by positivity : 0 < 1 + 2 * ε * (L₁ / 4) ^ 2 / (L₀ / 4)) hh
  simpa only [Real.log_pow, Nat.cast_ofNat] using hl

end LongTails.Proofs.GeneralizedSmoothTransientParameters
