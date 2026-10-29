import LongTails.Proofs.FeasibleGapTuning
import LongTails.Proofs.CompositeGapGrowth

namespace LongTails.Proofs.FeasibleGapGrowth

open LongTails.Setups.FeasibleHessianGapComposite
open OracleTemplate.FeasibleGapAccelerated
open FeasibleGapTuning

lemma log_mass_ratio {U D : ℝ} (hD : 1 ≤ D) (hDU : D ≤ U) :
    Real.log (131072 * Real.log (16 * U) ^ 2 * D) ≤ 8 * Real.log (16 * U) := by
  have hU : 1 ≤ U := hD.trans hDU
  have hL := logarithmic_scale hU
  have hLp : 0 < Real.log (16 * U) := by linarith
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1
    norm_num
  have hlogC : Real.log 131072 = 17 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 17 using 1
    norm_num
  have h16 := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
    (show 16 ≤ 16 * U by linarith)
  rw [hlog16] at h16
  have hDlog := Real.log_le_log (show 0 < D by linarith)
    (show D ≤ 16 * U by linarith)
  have hLL := Real.log_le_sub_one_of_pos hLp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogC]
  norm_num
  linarith

lemma iterations_suffice {U D B n : ℝ} (hD : 1 ≤ D) (hDU : D ≤ U)
    (hB : 1 / 2 ≤ B) (hn : 131072 * (1 + Real.sqrt U) * B ^ 2 ≤ n) :
    8 * B ≤ (n - 1) / (4096 * B * (1 + Real.sqrt D)) := by
  have hBp : 0 < B := by linarith
  have hS := Real.sqrt_le_sqrt hDU
  have hSn := Real.sqrt_nonneg D
  have hUn := Real.sqrt_nonneg U
  have hprod := mul_le_mul_of_nonneg_right hS (sq_nonneg B)
  have hBsq : 1 / 4 ≤ B ^ 2 := by nlinarith
  have hp : 0 ≤ Real.sqrt U * B ^ 2 := by positivity
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hn, hprod, hBsq, hp]

lemma active_mass (p : Params) {Δ A : ℝ} (hA : 0 < A) (hL : 1 / 2 ≤ logarithm p) :
    A + weight p Δ A = min (target p Δ) (A / (1 - fraction p Δ)) := by
  rw [weight, ite_eq_right hA.ne', ← min_add_add_left]
  have hd : 0 < 1 - fraction p Δ := by linarith [fraction_bound p hL Δ]
  congr 1
  · ring
  · field_simp
    ring

lemma phase_iterations_suffice (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) {d : ℝ} (hεd : p.ε ≤ d) :
    0 < phaseIterations p ∧ Real.log (131072 * logarithm p ^ 2 * scale p d) ≤
      ((phaseIterations p : ℝ) - 1) * fraction p d := by
  have hd : 0 < d := hε.trans_le hεd
  have hD := scale_ge_one p h0 h1 hR hd
  have hDU := scale_le_global p h0 hR hε hεd
  have hL := logarithm_lower p h0 h1 hε
  have hLp : 0 < logarithm p := by linarith
  have hN : 0 < phaseIterations p := Nat.ceil_pos.mpr (by
    change 0 < 131072 * (1 + Real.sqrt (globalScale p)) * logarithm p ^ 2
    positivity)
  refine ⟨hN, ?_⟩
  have hlog := log_mass_ratio hD hDU
  have hn : 131072 * (1 + Real.sqrt (globalScale p)) * logarithm p ^ 2 ≤
      (phaseIterations p : ℝ) := Nat.le_ceil _
  have hh := iterations_suffice hD hDU hL hn
  have ht := hlog.trans hh
  simpa only [fraction, logarithm, div_eq_mul_inv, one_div, one_mul] using ht

lemma stage_gap_gt (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    {k : ℕ} (hk : k < phases p) : p.ε < p.Δ / 2 ^ k := by
  have ht : (k : ℝ) < Real.log (p.Δ / p.ε) / Real.log 2 := Nat.lt_ceil.mp hk
  have hl : (k : ℝ) * Real.log 2 < Real.log (p.Δ / p.ε) :=
    (lt_div_iff₀ (Real.log_pos (by norm_num))).mp ht
  have he := Real.exp_lt_exp.mpr hl
  rw [Real.exp_log (show 0 < p.Δ / p.ε by positivity), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hh := (lt_div_iff₀ hε).mp he
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith only [hh]

lemma final_gap_le (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    p.Δ / 2 ^ phases p ≤ p.ε := by
  have ht : Real.log (p.Δ / p.ε) / Real.log 2 ≤ (phases p : ℝ) := Nat.le_ceil _
  have hl := (div_le_iff₀ (Real.log_pos (by norm_num))).mp ht
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (show 0 < p.Δ / p.ε by positivity), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hh := (div_le_iff₀ hε).mp he
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hh]


end LongTails.Proofs.FeasibleGapGrowth
