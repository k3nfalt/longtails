import LongTails.Proofs.GeneralizedFiniteSumParameters

namespace OracleTemplate.GeneralizedFiniteSum

open LongTails.Setups.GeneralizedSmoothFiniteSum

lemma log_two_plus_lower {H : ℝ} (hH : 0 ≤ H) : 1 / 2 ≤ Real.log (2 + H) := by
  have hh := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 2 + H)
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + H)
  simp only [one_div] at hi
  linarith

lemma trialCount_le (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    (trialCount p : ℝ) ≤ 6 * Real.log (2 + p.Δ / p.ε) := by
  let H := p.Δ / p.ε
  have hH : 0 < H := div_pos hΔ hε
  have h4 : 1 / 2 ≤ Real.log 4 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hh ⊢
    linarith
  have hX : 0 < 2 * max 1 H := by positivity
  have hlogX : 0 ≤ Real.log (2 * max 1 H) := Real.log_nonneg (by have := le_max_left (1 : ℝ) H; linarith)
  have hx : 2 * max 1 H ≤ (2 + H) ^ 2 := by
    rcases le_total H 1 with h | h
    · rw [max_eq_left h]
      nlinarith [sq_nonneg H]
    · rw [max_eq_right h]
      nlinarith [sq_nonneg H]
  have hl := Real.log_le_log hX hx
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hd : Real.log (2 * max 1 H) / Real.log 4 ≤ 4 * Real.log (2 + H) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 4)).mpr
    have hlog := log_two_plus_lower hH.le
    nlinarith [mul_nonneg (show 0 ≤ Real.log (2 + H) by linarith) (show 0 ≤ Real.log 4 - 1 / 2 by linarith)]
  have hc := (Nat.ceil_lt_add_one (div_nonneg hlogX (by linarith : 0 ≤ Real.log 4))).le
  change (trialCount p : ℝ) ≤ Real.log (2 * max 1 H) / Real.log 4 + 1 at hc
  have hell := log_two_plus_lower hH.le
  change (trialCount p : ℝ) ≤ 6 * Real.log (2 + H)
  linarith

lemma oracleCost_le (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1)
    (hG : 0 ≤ p.G) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    p.n + trialCount p * (2 * p.n * epochCount p + p.n) ≤
      ⌈16777216 * ((p.n : ℝ) * (1 + p.L1 * p.R) * Real.log (2 + p.Δ / p.ε) ^ 2 +
        Real.sqrt ((p.n : ℝ) * (p.L0 + p.L1 * p.G) * p.R ^ 2 / p.ε) * Real.log (2 + p.Δ / p.ε))⌉₊ := by
  let ell := Real.log (2 + p.Δ / p.ε)
  let Q := 1 + p.L1 * p.R
  let X := (p.L0 + p.L1 * p.G) * p.R ^ 2 / ((p.n : ℝ) * p.ε)
  let S := (p.n : ℝ) * Q * ell ^ 2 + (p.n : ℝ) * Real.sqrt X * ell
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hell : 1 / 2 ≤ ell := log_two_plus_lower (div_nonneg hΔ.le hε.le)
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [mul_nonneg h1 hR.le]
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hJ := trialCount_le p hΔ hε
  have hN : (epochCount p : ℝ) ≤ 65536 * Q * ell + 65536 * Real.sqrt X + 1 := by
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 65536 * Q * ell + 65536 * Real.sqrt X)).le
  have hsmall : 18 * (p.n : ℝ) * ell + p.n ≤ 40 * S := by
    have hq := mul_le_mul_of_nonneg_left hQ (mul_nonneg hn.le (sq_nonneg ell))
    have hsq : 18 * ell + 1 ≤ 40 * ell ^ 2 := by nlinarith [sq_nonneg (ell - 1 / 2)]
    have hh := mul_le_mul_of_nonneg_left hsq hn.le
    have hnoise : 0 ≤ (p.n : ℝ) * Real.sqrt X * ell := by positivity
    dsimp [S]
    nlinarith only [hq, hh, hnoise]
  have hcost : ((p.n + trialCount p * (2 * p.n * epochCount p + p.n) : ℕ) : ℝ) ≤ 16777216 * S := by
    calc
      _ = (p.n : ℝ) + trialCount p * (2 * p.n * epochCount p + p.n) := by push_cast; ring
      _ ≤ (p.n : ℝ) + (6 * ell) * (2 * p.n * (65536 * Q * ell + 65536 * Real.sqrt X + 1) + p.n) := by
        gcongr
      _ = 786432 * S + 18 * p.n * ell + p.n := by dsimp [S]; ring
      _ ≤ 16777216 * S := by nlinarith only [hsmall, hS]
  have hsqrt : (p.n : ℝ) * Real.sqrt X =
      Real.sqrt ((p.n : ℝ) * (p.L0 + p.L1 * p.G) * p.R ^ 2 / p.ε) := by
    calc
      _ = Real.sqrt ((p.n : ℝ) ^ 2) * Real.sqrt X := by rw [Real.sqrt_sq hn.le]
      _ = _ := by
        rw [← Real.sqrt_mul (sq_nonneg (p.n : ℝ))]
        congr 1
        dsimp [X]
        field_simp
  have hfinal : (16777216 : ℝ) * S ≤
      ⌈16777216 * ((p.n : ℝ) * (1 + p.L1 * p.R) * Real.log (2 + p.Δ / p.ε) ^ 2 +
        Real.sqrt ((p.n : ℝ) * (p.L0 + p.L1 * p.G) * p.R ^ 2 / p.ε) * Real.log (2 + p.Δ / p.ε))⌉₊ := by
    dsimp [S]
    rw [hsqrt]
    exact Nat.le_ceil _
  exact_mod_cast hcost.trans hfinal

end OracleTemplate.GeneralizedFiniteSum
