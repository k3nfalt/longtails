import LongTails.Algorithms.SmoothBanachAnchoring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace LongTails.Proofs.SmoothBanachTuning

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring

lemma strength_pos (q : Params) (j : ℕ) : 0 < strength q j := by
  unfold strength
  positivity

lemma strength_double (q : Params) (j : ℕ) : strength q (j + 1) = 2 * strength q j := by
  simp only [strength, pow_succ]
  ring

lemma strength_last (q : Params) : strength q (levels q) = 1 := by
  simp [strength]

lemma strength_initial_le (q : Params) (j : ℕ) : strength q 0 ≤ strength q j := by
  simp only [strength, pow_zero]
  exact div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)

lemma relaxation_pos (q : Params) (hC : 0 ≤ q.C) : 0 < relaxation q := by
  unfold relaxation
  positivity

lemma relaxation_le_one (q : Params) (hC : 0 ≤ q.C) : relaxation q ≤ 1 := by
  have hp : 0 ≤ 1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2 := by positivity
  have hpow : 0 < (2 : ℝ) ^ levels q := by positivity
  unfold relaxation
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

lemma innerSteps_pos (q : Params) (hC : 0 ≤ q.C) : 0 < innerSteps q := by
  unfold innerSteps
  apply Nat.ceil_pos.mpr
  exact div_pos (by positivity) (relaxation_pos q hC)

lemma innerSteps_contraction (q : Params) (hC : 0 ≤ q.C) :
    8 * (levels q + 1 : ℝ) ≤ relaxation q * innerSteps q := by
  have h := Nat.le_ceil (8 * (levels q + 1 : ℝ) / relaxation q)
  rw [div_le_iff₀ (relaxation_pos q hC)] at h
  simpa only [innerSteps, mul_comm] using h

lemma initial_strength_radius (q : Params) (hε : 0 < q.ε) :
    strength q 0 * q.R ≤ q.ε / 16 := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (⌈16 * q.R / q.ε⌉₊ + 1)
  have hc : (⌈16 * q.R / q.ε⌉₊ : ℝ) ≤ (2 : ℝ) ^ levels q := by
    have hn : ⌈16 * q.R / q.ε⌉₊ ≤ 2 ^ levels q := by
      exact (Nat.le_succ _).trans hp
    exact_mod_cast hn
  have hr : 16 * q.R / q.ε ≤ (2 : ℝ) ^ levels q := (Nat.le_ceil _).trans hc
  have hpow : 0 < (2 : ℝ) ^ levels q := by positivity
  rw [div_le_iff₀ hε] at hr
  simp only [strength, pow_zero]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  field_simp
  nlinarith

lemma contraction_geometric_sum (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    δ * ∑ j ∈ Finset.range n, ((1 - δ) ^ 2) ^ j ≤ 1 := by
  have hstrong : δ * ∑ j ∈ Finset.range n, ((1 - δ) ^ 2) ^ j ≤
      1 - ((1 - δ) ^ 2) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ ((1 - δ) ^ 2) n]
      have hp : 0 ≤ ((1 - δ) ^ 2) ^ n := pow_nonneg (sq_nonneg _) _
      have hc : (1 - δ) ^ 2 + δ ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hc hp]
  exact hstrong.trans (by nlinarith [pow_nonneg (sq_nonneg (1 - δ)) n])

lemma contraction_decay (δ S : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hS : 0 < S)
    (n : ℕ) (hn : 8 * S ≤ δ * n) :
    ((1 - δ) ^ 2) ^ n ≤ 1 / (64 * S ^ 2) := by
  have hc : (1 - δ) ^ 2 ≤ Real.exp (-δ) := by
    have he := Real.add_one_le_exp (-δ)
    nlinarith
  have hp := pow_le_pow_left₀ (sq_nonneg (1 - δ)) hc n
  have hexp : ((1 - δ) ^ 2) ^ n ≤ Real.exp (-(8 * S)) := by
    calc
      _ ≤ Real.exp (-δ) ^ n := hp
      _ = Real.exp ((n : ℝ) * (-δ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have he2 := Real.add_one_le_exp (2 * S)
  have h4 : 8 * S ≤ Real.exp (4 * S) := by
    have hp2 := (sq_le_sq₀ (by positivity : 0 ≤ 2 * S + 1)
      (Real.exp_nonneg (2 * S))).mpr he2
    have he4 : Real.exp (4 * S) = Real.exp (2 * S) ^ 2 := by
      rw [show 4 * S = 2 * S + 2 * S by ring, Real.exp_add]
      ring
    rw [he4]
    nlinarith [sq_nonneg (2 * S - 1)]
  have h8 : 64 * S ^ 2 ≤ Real.exp (8 * S) := by
    have hp4 := (sq_le_sq₀ (by positivity : 0 ≤ 8 * S)
      (Real.exp_nonneg (4 * S))).mpr h4
    have he8 : Real.exp (8 * S) = Real.exp (4 * S) ^ 2 := by
      rw [show 8 * S = 4 * S + 4 * S by ring, Real.exp_add]
      ring
    rw [he8]
    nlinarith
  apply hexp.trans
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h8

lemma relaxation_identity (q : Params) (hC : 0 ≤ q.C) :
    relaxation q * (1 + (2 : ℝ) ^ levels q +
      1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2) = 1 := by
  have hd : 0 < 1 + (2 : ℝ) ^ levels q +
      1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2 := by positivity
  simp only [relaxation, one_div, inv_mul_cancel₀ hd.ne']

lemma picard_step_size (q : Params) (hC : 0 ≤ q.C) (j : ℕ) :
    relaxation q / strength q j * (1 + strength q j) ≤ 1 := by
  have hd := relaxation_identity q hC
  have hr := (relaxation_pos q hC).le
  have hp : 0 ≤ 1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2 := by positivity
  have hb : relaxation q * (1 + (2 : ℝ) ^ levels q) ≤ 1 := by
    nlinarith [mul_nonneg hr hp]
  have ha := strength_pos q j
  have hpow : 1 ≤ strength q j * (2 : ℝ) ^ levels q := by
    have hn : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    simpa only [strength, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ levels q ≠ 0)] using hn
  rw [div_mul_eq_mul_div, div_le_iff₀ ha]
  nlinarith [mul_le_mul_of_nonneg_left hb ha.le, mul_le_mul_of_nonneg_left hpow hr]

lemma normalized_noise_floor (q : Params) (hC : 0 ≤ q.C) (hε : 0 < q.ε) :
    q.C * relaxation q * q.σ ^ 2 ≤ q.ε ^ 2 / (1024 * (levels q + 1 : ℝ) ^ 2) := by
  have hd := relaxation_identity q hC
  have hr := (relaxation_pos q hC).le
  have hb : relaxation q *
      (1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2) ≤ 1 := by
    have hp : 0 ≤ (2 : ℝ) ^ levels q := by positivity
    nlinarith [mul_nonneg hr hp]
  have he : relaxation q *
      (1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2) =
      (q.C * relaxation q * q.σ ^ 2 * (1024 * (levels q + 1 : ℝ) ^ 2)) / q.ε ^ 2 := by ring
  rw [he, div_le_iff₀ (sq_pos_of_pos hε)] at hb
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [one_mul] using hb

end LongTails.Proofs.SmoothBanachTuning
