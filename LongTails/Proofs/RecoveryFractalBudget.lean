import LongTails.Proofs.RecoveryFractalConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace LongTails.Proofs.RecoveryFractalBudget

open LongTails.Setups.SmoothHessianLipschitzGd LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalTuning LongTails.Proofs.RecoveryFractalExecution
open LongTails.Proofs.RecoveryFractalConvergence

lemma admissible_in_search (p : Params) (k : ℕ) (hk : admissibleLevel p k) :
    k ≤ Nat.log2 ⌈scaledGap p⌉₊ := by
  have hn : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hnX : (2 : ℝ) ^ k ≤ scaledGap p := by nlinarith [hk.2.1]
  have hreal := hnX.trans (Nat.le_ceil (scaledGap p))
  have hnat : 2 ^ k ≤ ⌈scaledGap p⌉₊ := by exact_mod_cast hreal
  have hpos : 0 < (2 : ℕ) ^ k := by positivity
  have hceil : ⌈scaledGap p⌉₊ ≠ 0 := by omega
  exact (Nat.le_log2 hceil).mpr hnat

lemma admissible_le_selected (p : Params) (k : ℕ) (hk : admissibleLevel p k) : k ≤ level p := by
  classical
  exact Nat.le_findGreatest (admissible_in_search p k hk) hk

noncomputable def comparisonLevel (p : Params) : ℕ := max 1 (level p)

lemma comparison_next_rejected (p : Params) : ¬ admissibleLevel p (comparisonLevel p + 1) := by
  intro hh
  have hle := admissible_le_selected p _ hh
  have hm : level p ≤ comparisonLevel p := le_max_right _ _
  omega

lemma comparisonLevel_one_le (p : Params) : 1 ≤ comparisonLevel p := le_max_left _ _

lemma comparison_log_bound (p : Params) (hX : 0 ≤ scaledGap p) :
    (comparisonLevel p : ℝ) + 8 ≤ 8 + Real.logb 2 (2 + scaledGap p) := by
  have hpow : (2 : ℝ) ^ comparisonLevel p ≤ 2 + scaledGap p := by
    by_cases hk : 2 ≤ level p
    · have he : comparisonLevel p = level p := max_eq_right (by omega)
      rw [he]
      have ha := selected_level_admissible p hk
      have hn : (1 : ℝ) ≤ 2 ^ level p := one_le_pow₀ (by norm_num)
      nlinarith [ha.2.1]
    · have he : comparisonLevel p = 1 := max_eq_left (by omega)
      rw [he]
      norm_num
      linarith
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2 ^ comparisonLevel p) hpow
  rw [Real.logb_pow] at hh
  norm_num at hh
  linarith

lemma logarithmic_factor_lower (X : ℝ) (hX : 0 ≤ X) : 9 ≤ 8 + Real.logb 2 (2 + X) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 2 + X by linarith)
  norm_num at hh
  linarith

lemma rpow_seventeen_half (x : ℝ) (hx : 0 < x) :
    x ^ (17 / 2 : ℝ) = x ^ 8 * Real.sqrt x := by
  rw [show (17 / 2 : ℝ) = (8 : ℝ) + 1 / 2 by norm_num, Real.rpow_add hx,
    show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

lemma epoch_cost_cap (p : Params) (hk : 2 ≤ level p) :
    (epochLength p : ℝ) ≤ repetitions p * scaledGap p / blockLength p := by
  have hn : 0 < (blockLength p : ℝ) := by exact_mod_cast blockLength_pos p
  have hc : (blockLength p : ℝ) ^ 2 ≤ scaledGap p := by
    simpa [blockLength] using (selected_level_admissible p hk).2.1
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ (repetitions p : ℝ) by positivity)
  apply (le_div_iff₀ hn).mpr
  unfold epochLength
  push_cast
  nlinarith only [hh]

lemma recoveryOverhead_cost_cap (p : Params) (hk : 2 ≤ level p) :
    recoveryOverhead p ≤ repetitions p * scaledGap p / blockLength p := by
  have hn : 0 < (blockLength p : ℝ) := by exact_mod_cast blockLength_pos p
  have hc : 65536 * curvatureScale p * (repetitions p : ℝ) ^ 2 *
      (blockLength p : ℝ) ^ (17 / 2 : ℝ) ≤ scaledGap p := by
    have hh := (selected_level_admissible p hk).2.2.2
    norm_num [repetitions, blockLength] at hh ⊢
    exact hh
  rw [rpow_seventeen_half _ hn] at hc
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ (repetitions p : ℝ) by positivity)
  apply (le_div_iff₀ hn).mpr
  unfold recoveryOverhead
  nlinarith only [hh]

lemma gap_rate_identity (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) :
    p.Δ / progressRate p = 1024 * repetitions p * scaledGap p / blockLength p := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  have hm : (repetitions p : ℝ) ≠ 0 := by unfold repetitions; positivity
  unfold progressRate scaledGap
  field_simp

lemma selectedBudget_bound (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hk : 2 ≤ level p) :
    (selectedBudget p : ℝ) ≤ 1028 * repetitions p * scaledGap p / blockLength p + 4 := by
  have hr := progressRate_pos p hL hε
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ p.Δ / progressRate p by positivity)).le
  have hN := epoch_cost_cap p hk
  have hO := recoveryOverhead_cost_cap p hk
  have hM := recoveryLength_upper p hρ hε.le
  rw [gap_rate_identity p hL hε] at hceil
  unfold selectedBudget maxGroup
  rw [gap_rate_identity p hL hε]
  push_cast
  simp only [div_eq_mul_inv] at hceil hN hO ⊢
  nlinarith only [hceil, hN, hO, hM]

lemma failed_gap_rate (X n m : ℝ) (hX : 0 ≤ X) (hn : 0 < n) (hm : 0 ≤ m)
    (hfail : X < (2 * n) ^ 2) : m * X / n ≤ 2 * m * Real.sqrt X := by
  have hs := Real.sq_sqrt hX
  have hroot : Real.sqrt X ≤ 2 * n := by nlinarith [Real.sqrt_nonneg X]
  have hh := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg X)
  have hh' : X ≤ 2 * n * Real.sqrt X := by nlinarith only [hh, hs]
  have hmul := mul_le_mul_of_nonneg_left hh' hm
  apply (div_le_iff₀ hn).mpr
  nlinarith only [hmul]

lemma failed_smooth_rate (X a n m : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ a) (hn : 0 < n)
    (hm : 1 ≤ m) (hfail : 1 / 2 ^ 28 < a * (m + 1) ^ 2 * (2 * n) ^ 6) :
    m * X / n ≤ 64 * m ^ (4 / 3 : ℝ) * X * a ^ (1 / 6 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hs : (m + 1) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ a * n ^ 6 by positivity)
  have hc : (1 : ℝ) ≤ 68719476736 * a * m ^ 2 * n ^ 6 := by
    norm_num at hfail
    nlinarith only [hfail, hh]
  have ha6 : (a ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = a := by
    rw [← Real.rpow_mul_natCast ha]
    norm_num
  have hm6 : (m ^ (1 / 3 : ℝ)) ^ (6 : ℕ) = m ^ 2 := by
    rw [← Real.rpow_mul_natCast hm0.le]
    norm_num
  have hroot : 1 ≤ 64 * a ^ (1 / 6 : ℝ) * m ^ (1 / 3 : ℝ) * n := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
    simp only [mul_pow, ha6, hm6, one_pow]
    norm_num
    exact hc
  have hm43 : m ^ (4 / 3 : ℝ) = m * m ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hm0, Real.rpow_one]
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤ m * X by positivity)
  apply (div_le_iff₀ hn).mpr
  rw [hm43]
  nlinarith only [hmul]

lemma failed_recovery_rate (X a n m : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ a) (hn : 0 < n)
    (hm : 1 ≤ m) (hfail : X < 65536 * a * (m + 1) ^ 2 * (2 * n) ^ (17 / 2 : ℝ)) :
    m * X / n ≤ 16 * m ^ (21 / 17 : ℝ) * X ^ (15 / 17 : ℝ) * a ^ (2 / 17 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hp : ((2 * n) ^ (17 / 2 : ℝ)) ^ (2 : ℕ) = (2 * n) ^ (17 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * n)]
    norm_num
  have hs := pow_le_pow_left₀ hX hfail.le 2
  simp only [mul_pow, hp, ← pow_mul] at hs
  have hm4 := pow_le_pow_left₀ (show 0 ≤ m + 1 by positivity) (show m + 1 ≤ 2 * m by linarith) 4
  have hm4' : (m + 1) ^ 4 ≤ 16 * m ^ 4 := by simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using hm4
  have hweighted := mul_le_mul_of_nonneg_left hm4' (show 0 ≤ 562949953421312 * a ^ 2 * n ^ 17 by positivity)
  have hpos : 0 ≤ a ^ 2 * m ^ 4 * n ^ 17 := by positivity
  have hc : X ^ 2 ≤ (16 : ℝ) ^ 17 * a ^ 2 * m ^ 4 * n ^ 17 := by
    norm_num at hs ⊢
    nlinarith only [hs, hweighted, hpos]
  have hX17 : (X ^ (2 / 17 : ℝ)) ^ (17 : ℕ) = X ^ 2 := by
    rw [← Real.rpow_mul_natCast hX]
    norm_num
  have ha17 : (a ^ (2 / 17 : ℝ)) ^ (17 : ℕ) = a ^ 2 := by
    rw [← Real.rpow_mul_natCast ha]
    norm_num
  have hm17 : (m ^ (4 / 17 : ℝ)) ^ (17 : ℕ) = m ^ 4 := by
    rw [← Real.rpow_mul_natCast hm0.le]
    norm_num
  have hroot : X ^ (2 / 17 : ℝ) ≤ 16 * a ^ (2 / 17 : ℝ) * m ^ (4 / 17 : ℝ) * n := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (17 : ℕ) ≠ 0) (by positivity)
    simp only [mul_pow, hX17, ha17, hm17]
    exact hc
  have hXsum : X ^ (2 / 17 : ℝ) * X ^ (15 / 17 : ℝ) = X := by
    rw [← Real.rpow_add_of_nonneg hX (by norm_num) (by norm_num)]
    norm_num
  have hmsum : m ^ (21 / 17 : ℝ) = m * m ^ (4 / 17 : ℝ) := by
    rw [show (21 / 17 : ℝ) = 1 + 4 / 17 by norm_num, Real.rpow_add hm0, Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_right hroot (show 0 ≤ m * X ^ (15 / 17 : ℝ) by positivity)
  have heq : X ^ (2 / 17 : ℝ) * (m * X ^ (15 / 17 : ℝ)) = m * X := by
    calc
      _ = m * (X ^ (2 / 17 : ℝ) * X ^ (15 / 17 : ℝ)) := by ring
      _ = _ := by rw [hXsum]
  rw [heq] at hh
  apply (div_le_iff₀ hn).mpr
  rw [hmsum]
  nlinarith only [hh]

lemma rejected_level_rate (p : Params) (k : ℕ) (hk : 1 ≤ k)
    (hX : 0 ≤ scaledGap p) (ha : 0 ≤ curvatureScale p) (hreject : ¬ admissibleLevel p (k + 1)) :
    ((k : ℝ) + 8) * scaledGap p / (2 : ℝ) ^ k ≤
      2 * ((k : ℝ) + 8) * Real.sqrt (scaledGap p) +
      64 * ((k : ℝ) + 8) ^ (4 / 3 : ℝ) * scaledGap p * curvatureScale p ^ (1 / 6 : ℝ) +
      16 * ((k : ℝ) + 8) ^ (21 / 17 : ℝ) * scaledGap p ^ (15 / 17 : ℝ) * curvatureScale p ^ (2 / 17 : ℝ) := by
  let n : ℝ := 2 ^ k
  let m : ℝ := k + 8
  have hn : 0 < n := by dsimp [n]; positivity
  have hm : 1 ≤ m := by
    dsimp [m]
    have hh : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hnnext : (2 : ℝ) ^ (k + 1) = 2 * n := by dsimp [n]; rw [pow_succ]; ring
  have hmnext : ((k + 1 : ℕ) : ℝ) + 8 = m + 1 := by dsimp [m]; push_cast; ring
  have hnot : ¬ ((2 * n) ^ 2 ≤ scaledGap p ∧
      curvatureScale p * (m + 1) ^ 2 * (2 * n) ^ 6 ≤ 1 / 2 ^ 28 ∧
      65536 * curvatureScale p * (m + 1) ^ 2 * (2 * n) ^ (17 / 2 : ℝ) ≤ scaledGap p) := by
    rintro ⟨h1, h2, h3⟩
    apply hreject
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hnnext]
      exact h1
    · rw [hnnext, hmnext]
      exact h2
    · rw [hnnext, hmnext]
      norm_num
      exact h3
  have hA : 0 ≤ 2 * m * Real.sqrt (scaledGap p) := by positivity
  have hB : 0 ≤ 64 * m ^ (4 / 3 : ℝ) * scaledGap p * curvatureScale p ^ (1 / 6 : ℝ) := by positivity
  have hC : 0 ≤ 16 * m ^ (21 / 17 : ℝ) * scaledGap p ^ (15 / 17 : ℝ) * curvatureScale p ^ (2 / 17 : ℝ) := by positivity
  change m * scaledGap p / n ≤ _
  by_cases h1 : (2 * n) ^ 2 ≤ scaledGap p
  · by_cases h2 : curvatureScale p * (m + 1) ^ 2 * (2 * n) ^ 6 ≤ 1 / 2 ^ 28
    · have h3 : scaledGap p < 65536 * curvatureScale p * (m + 1) ^ 2 * (2 * n) ^ (17 / 2 : ℝ) := by
        by_contra hh
        exact hnot ⟨h1, h2, le_of_not_gt hh⟩
      have hh := failed_recovery_rate (scaledGap p) (curvatureScale p) n m hX ha hn hm h3
      linarith
    · have hh := failed_smooth_rate (scaledGap p) (curvatureScale p) n m hX ha hn hm (lt_of_not_ge h2)
      linarith
  · have hh := failed_gap_rate (scaledGap p) n m hX hn (by linarith) (lt_of_not_ge h1)
    linarith

lemma logarithmic_rate_domination (H m X a : ℝ) (hH : 1 ≤ H) (hm : 1 ≤ m)
    (hmH : m ≤ H) (hX : 0 ≤ X) (ha : 0 ≤ a) :
    1028 * (2 * m * Real.sqrt X + 64 * m ^ (4 / 3 : ℝ) * X * a ^ (1 / 6 : ℝ) +
      16 * m ^ (21 / 17 : ℝ) * X ^ (15 / 17 : ℝ) * a ^ (2 / 17 : ℝ)) + 4 ≤
      262144 * H ^ (4 / 3 : ℝ) *
        (X * a ^ (1 / 6 : ℝ) + Real.sqrt X + X ^ (15 / 17 : ℝ) * a ^ (2 / 17 : ℝ) + 1) := by
  have hm0 : 0 ≤ m := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hm1 := hmH.trans (Real.self_le_rpow_of_one_le hH (by norm_num : (1 : ℝ) ≤ 4 / 3))
  have hm43 := Real.rpow_le_rpow hm0 hmH (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hm21 := (Real.rpow_le_rpow hm0 hmH (by norm_num : (0 : ℝ) ≤ 21 / 17)).trans
    (Real.rpow_le_rpow_of_exponent_le hH (by norm_num : (21 / 17 : ℝ) ≤ 4 / 3))
  have h1 := mul_le_mul_of_nonneg_right hm1 (Real.sqrt_nonneg X)
  have h2 := mul_le_mul_of_nonneg_right hm43 (show 0 ≤ X * a ^ (1 / 6 : ℝ) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hm21
    (show 0 ≤ X ^ (15 / 17 : ℝ) * a ^ (2 / 17 : ℝ) by positivity)
  have hp := Real.one_le_rpow hH (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hp1 : 0 ≤ H ^ (4 / 3 : ℝ) * Real.sqrt X := by positivity
  have hp2 : 0 ≤ H ^ (4 / 3 : ℝ) * X * a ^ (1 / 6 : ℝ) := by positivity
  have hp3 : 0 ≤ H ^ (4 / 3 : ℝ) * X ^ (15 / 17 : ℝ) * a ^ (2 / 17 : ℝ) := by positivity
  nlinarith only [h1, h2, h3, hp, hp1, hp2, hp3]

noncomputable def rateExpression (p : Params) : ℝ :=
  262144 * (8 + Real.logb 2 (2 + scaledGap p)) ^ (4 / 3 : ℝ) *
    (scaledGap p * curvatureScale p ^ (1 / 6 : ℝ) + Real.sqrt (scaledGap p) +
      scaledGap p ^ (15 / 17 : ℝ) * curvatureScale p ^ (2 / 17 : ℝ) + 1)

lemma comparison_rate_bound (p : Params) (hX : 0 ≤ scaledGap p) (ha : 0 ≤ curvatureScale p) :
    1028 * ((comparisonLevel p : ℝ) + 8) * scaledGap p / (2 : ℝ) ^ comparisonLevel p + 4 ≤ rateExpression p := by
  have hh := rejected_level_rate p (comparisonLevel p) (comparisonLevel_one_le p) hX ha (comparison_next_rejected p)
  have hm : 1 ≤ (comparisonLevel p : ℝ) + 8 := by
    have hp : 0 ≤ (comparisonLevel p : ℝ) := by positivity
    linarith
  have hH := logarithmic_factor_lower (scaledGap p) hX
  have hb := logarithmic_rate_domination (8 + Real.logb 2 (2 + scaledGap p))
    ((comparisonLevel p : ℝ) + 8) (scaledGap p) (curvatureScale p) (by linarith)
    hm (comparison_log_bound p hX) hX ha
  unfold rateExpression
  simp only [div_eq_mul_inv] at hh ⊢
  linarith

lemma selected_budget_rate (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hk : 2 ≤ level p) :
    selectedBudget p ≤ ⌈rateExpression p⌉₊ := by
  have hX : 0 ≤ scaledGap p := by unfold scaledGap; positivity
  have ha : 0 ≤ curvatureScale p := by unfold curvatureScale; positivity
  have hb := comparison_rate_bound p hX ha
  have hc : comparisonLevel p = level p := max_eq_right (by omega)
  rw [hc] at hb
  have hs := selectedBudget_bound p hL hρ hΔ hε hk
  have heq : (blockLength p : ℝ) = (2 : ℝ) ^ level p := by simp [blockLength]
  have hrep : (repetitions p : ℝ) = (level p : ℝ) + 8 := by simp [repetitions]
  rw [heq, hrep] at hs
  exact_mod_cast (hs.trans hb).trans (Nat.le_ceil (rateExpression p))

lemma fallback_budget_rate (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hk : level p < 2) :
    2 * p.L * p.Δ / p.ε ^ 2 < (⌈rateExpression p⌉₊ : ℝ) := by
  have hX : 0 ≤ scaledGap p := by unfold scaledGap; positivity
  have ha : 0 ≤ curvatureScale p := by unfold curvatureScale; positivity
  have hb := comparison_rate_bound p hX ha
  have hc : comparisonLevel p = 1 := max_eq_left (by omega)
  rw [hc] at hb
  norm_num at hb
  have hceil := Nat.le_ceil (rateExpression p)
  have heq : 2 * p.L * p.Δ / p.ε ^ 2 = 2 * scaledGap p := by unfold scaledGap; ring
  rw [heq]
  linarith

lemma rate_output_accuracy (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (O : OracleTemplate.Oracle p.E p.E)
    (hO : ∀ history x seed, O.answer history (0, x) seed = gradient f x)
    (K : ℕ) (hK : ⌈rateExpression p⌉₊ ≤ K) (seed : (method p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖gradient f (OracleTemplate.execute O (method p) (fun _ => K) seed ξ)‖ ≤ p.ε := by
  by_cases hk : 2 ≤ level p
  · exact selected_output_accuracy p hL hρ hε hk f hf hH hlip hgap O hO K
      ((selected_budget_rate p hL hρ hΔ hε hk).trans hK) seed ξ
  · exact fallback_output_accuracy p hL hε (by omega) f (hf.differentiable (by norm_num))
      hlip hgap O hO K ((fallback_budget_rate p hL hρ hΔ hε (by omega)).trans_le
        (by exact_mod_cast hK)) seed ξ

lemma leading_rate_expansion (L ρ Δ ε : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hε : 0 < ε) :
    (L * Δ / ε ^ 2) * (ρ * ε / L ^ 2) ^ (1 / 6 : ℝ) =
      Δ * L ^ (2 / 3 : ℝ) * ρ ^ (1 / 6 : ℝ) / ε ^ (11 / 6 : ℝ) := by
  have hLp : (L ^ (2 : ℕ)) ^ (1 / 6 : ℝ) = L ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast_mul hL.le]
    norm_num
  have hLsum : L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) = L := by
    rw [← Real.rpow_add hL]
    norm_num
  have hεsum : ε ^ (1 / 6 : ℝ) * ε ^ (11 / 6 : ℝ) = ε ^ 2 := by
    rw [← Real.rpow_add hε]
    norm_num
  rw [Real.div_rpow (mul_nonneg hρ hε.le) (sq_nonneg L), Real.mul_rpow hρ hε.le, hLp]
  have hLpow := (Real.rpow_pos_of_pos hL (1 / 3 : ℝ)).ne'
  have hεpow := (Real.rpow_pos_of_pos hε (11 / 6 : ℝ)).ne'
  field_simp
  linear_combination (L * Δ * ρ ^ (1 / 6 : ℝ)) * hεsum -
    (Δ * ρ ^ (1 / 6 : ℝ) * ε ^ 2) * hLsum

lemma square_root_rate_expansion (L Δ ε : ℝ) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) :
    Real.sqrt (L * Δ / ε ^ 2) = Real.sqrt (L * Δ) / ε := by
  rw [Real.sqrt_div (mul_nonneg hL hΔ), Real.sqrt_sq hε]

lemma mixed_rate_expansion (L ρ Δ ε : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (L * Δ / ε ^ 2) ^ (15 / 17 : ℝ) * (ρ * ε / L ^ 2) ^ (2 / 17 : ℝ) =
      L ^ (11 / 17 : ℝ) * Δ ^ (15 / 17 : ℝ) * ρ ^ (2 / 17 : ℝ) / ε ^ (28 / 17 : ℝ) := by
  have hεp : (ε ^ (2 : ℕ)) ^ (15 / 17 : ℝ) = ε ^ (30 / 17 : ℝ) := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num
  have hLp : (L ^ (2 : ℕ)) ^ (2 / 17 : ℝ) = L ^ (4 / 17 : ℝ) := by
    rw [← Real.rpow_natCast_mul hL.le]
    norm_num
  have hLsum : L ^ (11 / 17 : ℝ) * L ^ (4 / 17 : ℝ) = L ^ (15 / 17 : ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hεsum : ε ^ (2 / 17 : ℝ) * ε ^ (28 / 17 : ℝ) = ε ^ (30 / 17 : ℝ) := by
    rw [← Real.rpow_add hε]
    norm_num
  rw [Real.div_rpow (mul_nonneg hL.le hΔ) (sq_nonneg ε), Real.mul_rpow hL.le hΔ,
    Real.div_rpow (mul_nonneg hρ hε.le) (sq_nonneg L), Real.mul_rpow hρ hε.le, hεp, hLp]
  have hLpow := (Real.rpow_pos_of_pos hL (4 / 17 : ℝ)).ne'
  have hεpow := (Real.rpow_pos_of_pos hε (30 / 17 : ℝ)).ne'
  have hεpow' := (Real.rpow_pos_of_pos hε (28 / 17 : ℝ)).ne'
  field_simp
  linear_combination (L ^ (15 / 17 : ℝ) * Δ ^ (15 / 17 : ℝ) * ρ ^ (2 / 17 : ℝ)) * hεsum -
    (Δ ^ (15 / 17 : ℝ) * ρ ^ (2 / 17 : ℝ) * ε ^ (30 / 17 : ℝ)) * hLsum

lemma rateExpression_expanded (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    rateExpression p = 262144 * (8 + Real.logb 2 (2 + p.L * p.Δ / p.ε ^ 2)) ^ (4 / 3 : ℝ) *
      (p.Δ * p.L ^ (2 / 3 : ℝ) * p.ρ ^ (1 / 6 : ℝ) / p.ε ^ (11 / 6 : ℝ) +
        Real.sqrt (p.L * p.Δ) / p.ε +
        p.L ^ (11 / 17 : ℝ) * p.Δ ^ (15 / 17 : ℝ) * p.ρ ^ (2 / 17 : ℝ) / p.ε ^ (28 / 17 : ℝ) + 1) := by
  unfold rateExpression scaledGap curvatureScale
  rw [leading_rate_expansion p.L p.ρ p.Δ p.ε hL hρ hε,
    square_root_rate_expansion p.L p.Δ p.ε hL.le hΔ hε.le,
    mixed_rate_expansion p.L p.ρ p.Δ p.ε hL hρ hΔ hε]

end LongTails.Proofs.RecoveryFractalBudget
