import LongTails.Proofs.CompositeGapGrowth

namespace LongTails.Proofs.CompositeGapBudget

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate.CompositeGapAccelerated

lemma log_two_lower : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have hh := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num at hh ⊢
  exact hh

lemma log_three_lower : (1 : ℝ) ≤ Real.log 3 := by
  have hh := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at hh ⊢
  exact hh

lemma sqrt_log_bound {B U : ℝ} (hB : 0 ≤ B) (hU : 1 ≤ U) (hUB : U ≤ 1 + 2 * B) :
    256 * (1 + Real.sqrt U) * Real.log (32 * U) ≤
      1536 * ((1 + Real.sqrt B) * Real.log (4 + B)) := by
  have hs : 1 + Real.sqrt U ≤ 2 * (1 + Real.sqrt B) := by
    have hsu := Real.sq_sqrt (show 0 ≤ U by linarith)
    have hsb := Real.sq_sqrt hB
    have hnu := Real.sqrt_nonneg U
    have hnb := Real.sqrt_nonneg B
    have hh : Real.sqrt U ≤ 1 + 2 * Real.sqrt B := by
      apply (sq_le_sq₀ hnu (by positivity)).mp
      nlinarith
    linarith
  have hl : Real.log (32 * U) ≤ 3 * Real.log (4 + B) := by
    have hp : 32 * U ≤ (4 + B) ^ 3 := by
      nlinarith [sq_nonneg (B - 2 / 3), pow_nonneg hB 3]
    have hh := Real.log_le_log (show 0 < 32 * U by positivity) hp
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  have hln : 0 ≤ Real.log (32 * U) := Real.log_nonneg (by linarith)
  have hprod := mul_le_mul hs hl hln (by positivity)
  nlinarith only [hprod]

lemma complexity_factor_one {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ (1 + Real.sqrt B) * Real.log (4 + B) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ 4 + B by linarith)
  have hl : 1 ≤ Real.log (4 + B) := log_three_lower.trans hh
  have hp := mul_nonneg (Real.sqrt_nonneg B) (show 0 ≤ Real.log (4 + B) by linarith)
  nlinarith

lemma rounded_iterations_bound {B U : ℝ} (hB : 0 ≤ B) (hU : 1 ≤ U) (hUB : U ≤ 1 + 2 * B) :
    (⌈256 * (1 + Real.sqrt U) * Real.log (32 * U)⌉₊ : ℝ) ≤
      1537 * ((1 + Real.sqrt B) * Real.log (4 + B)) := by
  have hl : 0 ≤ Real.log (32 * U) := Real.log_nonneg (by linarith)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 256 * (1 + Real.sqrt U) * Real.log (32 * U) by positivity)
  have hb := sqrt_log_bound hB hU hUB
  have hc := complexity_factor_one hB
  linarith

lemma rounded_phases_bound {r : ℝ} (hr : 1 < r) :
    (⌈Real.log r / Real.log 2⌉₊ : ℝ) ≤ (5 / 2) * Real.log (2 + r) := by
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr.le
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ Real.log r / Real.log 2 by positivity)
  have ht : Real.log r / Real.log 2 ≤ (3 / 2) * Real.log r := by
    apply (div_le_iff₀ htwo).mpr
    have hm := mul_le_mul_of_nonneg_left log_two_lower hlog
    nlinarith only [hm]
  have hl := Real.log_le_log (by linarith : 0 < r) (show r ≤ 2 + r by linarith)
  have hthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ 2 + r by linarith)
  linarith [log_three_lower]

lemma calls_bound (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hR : 0 < p.R)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    calls p ≤ ⌈8192 * (1 + p.R * Real.sqrt (p.H0 / p.ε + p.H1)) *
      Real.log (4 + p.R ^ 2 * (p.H0 / p.ε + p.H1)) * Real.log (2 + p.Δ / p.ε)⌉₊ := by
  by_cases hr : p.Δ / p.ε ≤ 1
  · have hl := Real.log_nonpos (show 0 ≤ p.Δ / p.ε by positivity) hr
    have hs : phases p = 0 := Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hl (Real.log_nonneg (by norm_num)))
    simp [calls, hs]
  · have hr' : 1 < p.Δ / p.ε := lt_of_not_ge hr
    let B := p.R ^ 2 * (p.H0 / p.ε + p.H1)
    let U := 1 + 2 * p.H0 * p.R ^ 2 / p.ε + p.H1 * p.R ^ 2
    let C := (1 + Real.sqrt B) * Real.log (4 + B)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hU : 1 ≤ U := by
      have hh : 0 ≤ 2 * p.H0 * p.R ^ 2 / p.ε := by positivity
      have ht : 0 ≤ p.H1 * p.R ^ 2 := by positivity
      dsimp [U]
      linarith
    have hUB : U ≤ 1 + 2 * B := by
      dsimp [U, B]
      have hh : 0 ≤ p.H1 * p.R ^ 2 := by positivity
      ring_nf at hh ⊢
      linarith only [hh]
    have hN : (phaseIterations p : ℝ) ≤ 1537 * C := rounded_iterations_bound hB hU hUB
    have hS := rounded_phases_bound hr'
    change (phases p : ℝ) ≤ (5 / 2) * Real.log (2 + p.Δ / p.ε) at hS
    have hC : 1 ≤ C := complexity_factor_one hB
    have hprod := mul_le_mul hN hS (Nat.cast_nonneg _) (show 0 ≤ 1537 * C by positivity)
    have hlog : 0 ≤ Real.log (2 + p.Δ / p.ε) := Real.log_nonneg (by linarith)
    have hc : (calls p : ℝ) ≤ 8192 * C * Real.log (2 + p.Δ / p.ε) := by
      dsimp [calls]
      push_cast
      have hh := mul_nonneg (show 0 ≤ C by linarith) hlog
      nlinarith only [hprod, hh]
    have hsqrt : Real.sqrt B = p.R * Real.sqrt (p.H0 / p.ε + p.H1) := by
      dsimp [B]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR.le]
    dsimp [C, B] at hc
    rw [hsqrt] at hc
    apply (Nat.cast_le (α := ℝ)).mp
    apply hc.trans
    simpa only [mul_assoc] using (Nat.le_ceil (8192 * (1 + p.R * Real.sqrt (p.H0 / p.ε + p.H1)) *
      Real.log (4 + p.R ^ 2 * (p.H0 / p.ε + p.H1)) * Real.log (2 + p.Δ / p.ε)))

end LongTails.Proofs.CompositeGapBudget
