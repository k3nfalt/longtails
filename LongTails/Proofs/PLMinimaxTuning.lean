import LongTails.Proofs.TwoSidedPLBudget
import LongTails.Algorithms.PLMinimaxMethod

namespace OracleTemplate.PLMinimax

lemma geometric_log_bound {C A : ℝ} (hC : 1 ≤ C) (hA : 0 < A) (n : ℕ)
    (hn : C * Real.log A ≤ n) : (1 - 1 / C) ^ n ≤ 1 / A := by
  have hC0 : 0 < C := by linarith
  apply (TwoSidedPL.pow_le_exp_window hC n).trans
  rw [one_div, ← Real.exp_log hA, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hh : Real.log A ≤ (n : ℝ) / C := (le_div_iff₀ hC0).mpr (by nlinarith [hn])
  linarith

lemma primal_iterations_suffice {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (n : ℕ)
    (hn : 18 * Real.log (12 * Real.sqrt (L / μ)) ≤ n) :
    144 * L * ((17 / 18 : ℝ) ^ n) ^ 2 ≤ μ := by
  have hL : 0 < L := hμ.trans_le hμL
  have hk : 0 < L / μ := div_pos hL hμ
  have hs : 0 < Real.sqrt (L / μ) := Real.sqrt_pos.mpr hk
  have hh := geometric_log_bound (C := 18) (A := 12 * Real.sqrt (L / μ))
    (by norm_num) (by positivity) n hn
  rw [show (1 - 1 / (18 : ℝ)) = 17 / 18 by norm_num] at hh
  have hsq := pow_le_pow_left₀ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 17 / 18) n) hh 2
  have he : (1 / (12 * Real.sqrt (L / μ))) ^ 2 = μ / (144 * L) := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hk.le]
    field_simp [hL.ne', hμ.ne']
    norm_num
  rw [he] at hsq
  have hb := (le_div_iff₀ (show 0 < 144 * L by positivity)).mp hsq
  nlinarith

lemma dual_iterations_suffice {L μ S τ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hS : 0 ≤ S) (hτ : 0 < τ) (n : ℕ)
    (hn : (4 * L / μ) * Real.log (1 + 64 * L * S / τ ^ 2) ≤ n) :
    (1 - μ / (4 * L)) ^ n * (S + τ ^ 2 / (64 * L)) ≤ τ ^ 2 / (64 * L) := by
  have hL : 0 < L := hμ.trans_le hμL
  have hC : 1 ≤ 4 * L / μ := by rw [le_div_iff₀ hμ]; linarith
  have hA : 0 < 1 + 64 * L * S / τ ^ 2 := by positivity
  have hh := geometric_log_bound hC hA n hn
  have he : 1 / (4 * L / μ) = μ / (4 * L) := by field_simp [hL.ne', hμ.ne']
  rw [he] at hh
  have hs : 0 ≤ S + τ ^ 2 / (64 * L) := by positivity
  apply (mul_le_mul_of_nonneg_right hh hs).trans
  have hid : (1 / (1 + 64 * L * S / τ ^ 2)) * (S + τ ^ 2 / (64 * L)) = τ ^ 2 / (64 * L) := by
    field_simp [hL.ne', hτ.ne']
    ring
  exact hid.le

lemma tuning_positive {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p) :
    0 < (tuning p).smoothness ∧ 0 < (tuning p).curvature ∧ 0 < (tuning p).mesh ∧
    0 < (tuning p).accuracy ∧ 0 < (tuning p).threshold ∧
    0 < (tuning p).gradientTolerance ∧ 0 < (tuning p).hessianTolerance ∧
    0 < (tuning p).regularization ∧ 0 < (tuning p).distanceTolerance ∧
    0 < (tuning p).residualTolerance := by
  have hμ := hv.1
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  dsimp [tuning]
  repeat' constructor
  all_goals positivity

lemma tuning_threshold_bounds {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p) :
    (tuning p).smoothness * (tuning p).threshold ^ 2 ≤ p.ε / 16 ∧
    (tuning p).smoothness * (tuning p).threshold ≤ (tuning p).curvature / 8 ∧
    (tuning p).threshold ≤ (tuning p).mesh := by
  have hp := tuning_positive hv
  have hM := hp.1
  have hη := hp.2.1
  have hm := hp.2.2.1
  have ha := hp.2.2.2.1
  have ht := hp.2.2.2.2.1
  have he : (tuning p).accuracy ≤ p.ε := by dsimp [tuning]; exact min_le_left _ _
  have hc : (tuning p).accuracy ≤ (tuning p).curvature ^ 2 / (4 * (tuning p).smoothness) := by
    dsimp [tuning]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hb : (tuning p).accuracy ≤ 16 * (tuning p).smoothness * (tuning p).mesh ^ 2 := by
    dsimp [tuning]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hs : (tuning p).threshold ^ 2 = (tuning p).accuracy / (16 * (tuning p).smoothness) := by
    change (Real.sqrt ((tuning p).accuracy / (16 * (tuning p).smoothness))) ^ 2 = _
    exact Real.sq_sqrt (by positivity)
  have hse : 16 * (tuning p).smoothness * (tuning p).threshold ^ 2 = (tuning p).accuracy := by
    rw [hs]
    field_simp
  have hc' := (le_div_iff₀ (show 0 < 4 * (tuning p).smoothness by positivity)).mp hc
  refine ⟨by linarith only [hse, he], ?_, ?_⟩
  · apply (sq_le_sq₀ (mul_nonneg hM.le ht.le) (show 0 ≤ (tuning p).curvature / 8 by positivity)).mp
    have hh := congrArg (fun a : ℝ => a * (4 * (tuning p).smoothness)) hse
    nlinarith only [hh, hc']
  · apply (sq_le_sq₀ ht.le hm.le).mp
    nlinarith only [hse, hb, hM]

lemma tuning_distance_bounds (p : LongTails.Setups.NonconvexPLSecondOrder.Params) :
    (tuning p).distanceTolerance ≤ p.μ / (128 * p.ρ) ∧
    (tuning p).distanceTolerance ≤ (tuning p).gradientTolerance / (2 * p.L) ∧
    (tuning p).distanceTolerance ≤ (tuning p).hessianTolerance /
      (8 * p.L ^ 2 * p.ρ * ((tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2)) ∧
    (tuning p).distanceTolerance ≤ p.ε / (8 * p.L * (p.L / p.μ)) ∧
    (tuning p).distanceTolerance ≤ (tuning p).curvature /
      (2 * (tuning p).smoothness * (1 + 2 * p.L / p.μ) ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [tuning]; simp only [mul_div_assoc]; exact min_le_left _ _
  · dsimp [tuning]; simp only [mul_div_assoc]; exact (min_le_right _ _).trans (min_le_left _ _)
  · dsimp [tuning]; simp only [mul_div_assoc]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · dsimp [tuning]; simp only [mul_div_assoc]; exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · dsimp [tuning]; simp only [mul_div_assoc]; exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

lemma tuning_hessian_bias {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p) :
    4 * p.L ^ 2 * (tuning p).regularization * (4 + 32 * p.L / p.μ) ^ 2 =
      ((tuning p).hessianTolerance / 2) ^ 4 := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hC : 0 < 4 + 32 * p.L / p.μ := by have := hv.1; positivity
  change 4 * p.L ^ 2 * ((tuning p).hessianTolerance ^ 4 /
    (64 * p.L ^ 2 * (4 + 32 * (p.L / p.μ)) ^ 2)) * (4 + 32 * p.L / p.μ) ^ 2 = _
  rw [show 4 + 32 * (p.L / p.μ) = 4 + 32 * p.L / p.μ by ring]
  generalize 4 + 32 * p.L / p.μ = C at hC ⊢
  field_simp [hL.ne', hC.ne']
  ring

lemma halving_log_bound {A : ℝ} (hA : 0 < A) (n : ℕ)
    (hn : Real.log A / Real.log 2 ≤ n) : (1 / 2 : ℝ) ^ n ≤ 1 / A := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := (div_le_iff₀ hlog).mp hn
  calc
    (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2) ^ n := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ = Real.exp (-((n : ℝ) * Real.log 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log A) := Real.exp_le_exp.mpr (by linarith only [hh])
    _ = 1 / A := by rw [Real.exp_neg, Real.exp_log hA, one_div]

lemma refinement_iterations_suffice {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ) (n : ℕ)
    (hn : Real.log (1 + B / τ) / Real.log 2 ≤ n) :
    B * ((1 / 2 : ℝ) ^ n) ^ 2 ≤ τ := by
  have hA : 0 < 1 + B / τ := by positivity
  have hq := halving_log_bound hA n hn
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hq1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs : ((1 / 2 : ℝ) ^ n) ^ 2 ≤ (1 / 2 : ℝ) ^ n := by nlinarith only [hq0, hq1]
  have hh := mul_le_mul_of_nonneg_left (hs.trans hq) hB
  apply hh.trans
  rw [mul_one_div, div_le_iff₀ hA]
  have he : τ * (1 + B / τ) = τ + B := by field_simp [hτ.ne']
  rw [he]
  linarith only [hτ]

lemma tuning_primal_iterations {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p) :
    144 * p.L * ((17 / 18 : ℝ) ^ (tuning p).primalSteps) ^ 2 ≤ p.μ := by
  apply primal_iterations_suffice hv.1 hv.2.1
  exact Nat.le_ceil _

lemma tuning_dual_iterations {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p) :
    (1 - p.μ / (4 * p.L)) ^ (tuning p).dualSteps *
      (32 * (p.L / p.μ) * (p.Δ + p.D) + (tuning p).residualTolerance ^ 2 / (64 * p.L)) ≤
        (tuning p).residualTolerance ^ 2 / (64 * p.L) := by
  have hp := tuning_positive hv
  have hτ := hp.2.2.2.2.2.2.2.2.2
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hS : 0 ≤ 32 * (p.L / p.μ) * (p.Δ + p.D) := by
    have hΔ := hv.2.2.2.1
    have hD := hv.2.2.2.2.1
    have hμ := hv.1
    positivity
  apply dual_iterations_suffice hv.1 hv.2.1 hS hτ
  have hn := Nat.le_ceil (4 * (p.L / p.μ) * Real.log
    (1 + 64 * p.L * (32 * (p.L / p.μ) * (p.Δ + p.D)) / (tuning p).residualTolerance ^ 2))
  convert hn using 1
  · ring
  · rfl

lemma segment_count_bound {r mesh : ℝ} (hr : 0 ≤ r) (hm : 0 < mesh) :
    ((max 1 ⌈r / mesh⌉₊ : ℕ) : ℝ) ≤ 2 + (r / mesh) ^ 3 := by
  have ht : 0 ≤ r / mesh := div_nonneg hr hm.le
  have hc := (Nat.ceil_lt_add_one ht).le
  have hpow : 0 ≤ (r / mesh) ^ 3 := pow_nonneg ht _
  have hh : r / mesh ≤ 1 + (r / mesh) ^ 3 := by
    by_cases h : r / mesh ≤ 1
    · linarith only [h, hpow]
    · have h' : 1 ≤ r / mesh := (lt_of_not_ge h).le
      have hp := mul_nonneg (sub_nonneg.mpr h')
        (show 0 ≤ (r / mesh) * (r / mesh + 1) by positivity)
      nlinarith only [hp]
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith only [hpow]) (by linarith only [hc, hh])

lemma terminal_segment_count {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p) (d : p.E)
    (hd : ‖d‖ ≤ (tuning p).threshold) : max 1 ⌈‖d‖ / (tuning p).mesh⌉₊ = 1 := by
  apply max_eq_left
  apply Nat.ceil_le.mpr
  simp only [Nat.cast_one]
  exact (div_le_one (tuning_positive hv).2.2.1).mpr
    (hd.trans (tuning_threshold_bounds hv).2.2)

end OracleTemplate.PLMinimax
