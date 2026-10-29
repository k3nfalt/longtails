import LongTails.Proofs.FeasibleGapGrowth
import LongTails.Proofs.CompositeGapBudget

namespace LongTails.Proofs.FeasibleGapBudget

open LongTails.Setups.FeasibleHessianGapComposite
open OracleTemplate.FeasibleGapAccelerated

lemma sqrt_log_bound {B U : ℝ} (hB : 0 ≤ B) (hU : 1 ≤ U) (hUB : U ≤ 1 + 2 * B) :
    131072 * (1 + Real.sqrt U) * Real.log (16 * U) ^ 2 ≤
      2359296 * ((1 + Real.sqrt B) * Real.log (4 + B) ^ 2) := by
  have hs : 1 + Real.sqrt U ≤ 2 * (1 + Real.sqrt B) := by
    have hsu := Real.sq_sqrt (show 0 ≤ U by linarith)
    have hsb := Real.sq_sqrt hB
    have hnu := Real.sqrt_nonneg U
    have hnb := Real.sqrt_nonneg B
    have hh : Real.sqrt U ≤ 1 + 2 * Real.sqrt B := by
      apply (sq_le_sq₀ hnu (by positivity)).mp
      nlinarith
    linarith
  have hl : Real.log (16 * U) ≤ 3 * Real.log (4 + B) := by
    have hp : 16 * U ≤ (4 + B) ^ 3 := by
      nlinarith [sq_nonneg (B - 2 / 3), pow_nonneg hB 3]
    have hh := Real.log_le_log (show 0 < 16 * U by positivity) hp
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  have hln : 0 ≤ Real.log (16 * U) := Real.log_nonneg (by linarith)
  have hlB : 0 ≤ Real.log (4 + B) := Real.log_nonneg (by linarith)
  have hl2 := (sq_le_sq₀ hln (by positivity)).mpr hl
  have hprod := mul_le_mul hs hl2 (sq_nonneg _) (by positivity)
  nlinarith only [hprod]

lemma complexity_factor_one {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ (1 + Real.sqrt B) * Real.log (4 + B) ^ 2 := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ 4 + B by linarith)
  have hl : 1 ≤ Real.log (4 + B) := CompositeGapBudget.log_three_lower.trans hh
  have hlsq : 1 ≤ Real.log (4 + B) ^ 2 := by nlinarith
  have hp := mul_nonneg (Real.sqrt_nonneg B) (sq_nonneg (Real.log (4 + B)))
  nlinarith

lemma rounded_iterations_bound {B U : ℝ} (hB : 0 ≤ B) (hU : 1 ≤ U) (hUB : U ≤ 1 + 2 * B) :
    (⌈131072 * (1 + Real.sqrt U) * Real.log (16 * U) ^ 2⌉₊ : ℝ) ≤
      2359297 * ((1 + Real.sqrt B) * Real.log (4 + B) ^ 2) := by
  have hl : 0 ≤ Real.log (16 * U) := Real.log_nonneg (by linarith)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 131072 * (1 + Real.sqrt U) * Real.log (16 * U) ^ 2 by positivity)
  have hb := sqrt_log_bound hB hU hUB
  have hc := complexity_factor_one hB
  linarith

lemma calls_bound (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hR : 0 < p.R)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    calls p ≤ ⌈16777216 * (1 + p.R * Real.sqrt (p.H0 / p.ε + p.H1)) *
      Real.log (4 + p.R ^ 2 * (p.H0 / p.ε + p.H1)) ^ 2 * Real.log (2 + p.Δ / p.ε)⌉₊ := by
  by_cases hr : p.Δ / p.ε ≤ 1
  · have hl := Real.log_nonpos (show 0 ≤ p.Δ / p.ε by positivity) hr
    have hs : phases p = 0 := Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hl (Real.log_nonneg (by norm_num)))
    simp [calls, hs]
  · have hr' : 1 < p.Δ / p.ε := lt_of_not_ge hr
    let B := p.R ^ 2 * (p.H0 / p.ε + p.H1)
    let U := globalScale p
    let C := (1 + Real.sqrt B) * Real.log (4 + B) ^ 2
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hU : 1 ≤ U := FeasibleGapTuning.globalScale_ge_one p h0 h1 hε
    have hUB : U ≤ 1 + 2 * B := by
      dsimp [U, globalScale, B]
      have hh : 0 ≤ p.H1 * p.R ^ 2 := by positivity
      have ht : 0 ≤ p.H0 * p.R ^ 2 / p.ε := by positivity
      ring_nf at hh ht ⊢
      linarith only [hh, ht]
    have hN : (phaseIterations p : ℝ) ≤ 2359297 * C := rounded_iterations_bound hB hU hUB
    have hS := CompositeGapBudget.rounded_phases_bound hr'
    change (phases p : ℝ) ≤ (5 / 2) * Real.log (2 + p.Δ / p.ε) at hS
    have hC : 1 ≤ C := complexity_factor_one hB
    have hprod := mul_le_mul hN hS (Nat.cast_nonneg _) (show 0 ≤ 2359297 * C by positivity)
    have hlog : 0 ≤ Real.log (2 + p.Δ / p.ε) := Real.log_nonneg (by linarith)
    have hc : (calls p : ℝ) ≤ 16777216 * C * Real.log (2 + p.Δ / p.ε) := by
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
    convert (Nat.le_ceil (16777216 * (1 + p.R * Real.sqrt (p.H0 / p.ε + p.H1)) *
      Real.log (4 + p.R ^ 2 * (p.H0 / p.ε + p.H1)) ^ 2 * Real.log (2 + p.Δ / p.ε))) using 1
    congr 1
    ring


end LongTails.Proofs.FeasibleGapBudget
