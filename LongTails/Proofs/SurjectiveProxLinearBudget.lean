import LongTails.Proofs.SurjectiveProxLinearTuning

namespace LongTails.Proofs.SurjectiveProxLinearBudget

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearTuning
open LongTails.Proofs.SurjectiveProxLinearModel

lemma batch_budgets (p : Params) (hp : spec.valid p) :
    (initialBatch p : ℝ) ≤ 2 + 2 ^ 32 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 ∧
    (certificateBatch p : ℝ) ≤ 2 + 2 ^ 31 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 := by
  have hm : (p.m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.1).ne'
  have hH : p.H ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.2.1).ne'
  have hε := hp.2.2.2.2.1
  have hC := (variance_scales_positive p hp).1
  have h0 : 1024 * sensitivity p * p.σ ^ 2 / radius p ^ 2 =
      2 ^ 32 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 := by
    unfold sensitivity radius
    field_simp [hm, hH, hε.ne']
    ring
  have h1 : 8 * p.σ ^ 2 / certificateError p ^ 2 =
      2 ^ 31 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 := by
    unfold certificateError
    field_simp [hm, hH, hε.ne']
    ring
  constructor
  · have h := Nat.ceil_lt_add_one (show 0 ≤ 1024 * sensitivity p * p.σ ^ 2 / radius p ^ 2 by positivity)
    unfold initialBatch
    push_cast
    rw [h0] at h ⊢
    linarith
  · have h := Nat.ceil_lt_add_one (show 0 ≤ 8 * p.σ ^ 2 / certificateError p ^ 2 by positivity)
    unfold certificateBatch
    push_cast
    rw [h1] at h ⊢
    linarith

lemma gamma_lower (p : Params) (hp : spec.valid p) : 4 * p.m * p.H ^ 3 ≤ gamma p := by
  have hm : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  unfold gamma rho
  nlinarith [mul_nonneg hm (sq_nonneg p.H)]

lemma iteration_budget (p : Params) (hp : spec.valid p) :
    (iterations p : ℝ) ≤ 65 +
      2 ^ 29 * p.m ^ 2 * p.H ^ 10 * p.Δ / p.ε ^ 2 +
      2 ^ 43 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 +
      2 ^ 48 * p.m ^ 4 * p.H ^ 19 * p.Δ * p.σ / p.ε ^ 3 := by
  have hm : (0 : ℝ) < p.m := Nat.cast_pos.mpr hp.1
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one hp.2.1
  have hε := hp.2.2.2.2.1
  have hσ := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hsc := variance_scales_positive p hp
  have hγ := (valid_tuning_positive p hp).2.1
  have hθ := hsc.2.2.2.2.2
  have hr := hsc.2.1
  have hb := hsc.2.2.2.1
  have hgden : 4 * p.m * p.H ^ 3 * relaxation p * radius p ^ 2 ≤
      gamma p * relaxation p * radius p ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (gamma_lower p hp) hθ.le)
      (sq_nonneg _)
  have hgap := div_le_div_of_nonneg_left (show 0 ≤ 1024 * p.Δ by positivity)
    (show 0 < 4 * p.m * p.H ^ 3 * relaxation p * radius p ^ 2 by positivity) hgden
  have hid : 1024 * p.Δ / (4 * p.m * p.H ^ 3 * relaxation p * radius p ^ 2) =
      2 ^ 29 * p.m ^ 2 * p.H ^ 10 * p.Δ / p.ε ^ 2 +
      2 ^ 48 * p.m ^ 4 * p.H ^ 19 * p.Δ * p.σ / p.ε ^ 3 := by
    have hden : 1 + 524288 * p.m ^ 2 * p.H ^ 9 * p.σ / p.ε ≠ 0 := by positivity
    unfold relaxation radius
    field_simp [hm.ne', hH.ne', hε.ne', hden]
    ring
  rw [hid] at hgap
  have hbeta : 64 / beta p = 64 +
      2 ^ 43 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 := by
    unfold beta
    simp only [one_div, div_inv_eq_mul]
    unfold sensitivity radius
    field_simp [hm.ne', hH.ne', hε.ne']
    ring
  have hc := Nat.ceil_lt_add_one (show 0 ≤
      1024 * p.Δ / (gamma p * relaxation p * radius p ^ 2) + 64 / beta p by positivity)
  change (iterations p : ℝ) < _ at hc
  rw [hbeta] at hc
  linarith

lemma total_call_budget (p : Params) (hp : spec.valid p) :
    initialBatch p + iterations p + certificateBatch p ≤
      ⌈69 + (2 ^ 29 * p.m ^ 2 * p.H ^ 10 * p.Δ +
        2 ^ 44 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2) / p.ε ^ 2 +
        2 ^ 48 * p.m ^ 4 * p.H ^ 19 * p.Δ * p.σ / p.ε ^ 3⌉₊ := by
  have h0 := (batch_budgets p hp).1
  have h1 := (batch_budgets p hp).2
  have hT := iteration_budget p hp
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans _ (Nat.le_ceil _)
  push_cast
  have hn : 0 ≤ (p.m : ℝ) ^ 4 * p.H ^ 18 * p.σ ^ 2 / p.ε ^ 2 := by positivity
  rw [add_div]
  ring_nf at h0 h1 hT hn ⊢
  linarith

end LongTails.Proofs.SurjectiveProxLinearBudget
