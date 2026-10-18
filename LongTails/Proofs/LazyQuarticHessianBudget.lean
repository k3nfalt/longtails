import LongTails.Proofs.LazyQuarticLedger
import LongTails.Proofs.LazyQuarticRates

namespace LongTails.Proofs.LazyQuarticHessianBudget

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Proofs.LazyQuarticLedger

lemma metric_charge_identity (p : Params) (hp : spec.valid p) :
    (radius p * Real.sqrt (alpha p / (64 * beta p) * decrease p)) ^ 2 * condition p ^ 3 =
      p.Δ ^ 2 / (3 * 2 ^ 32) := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hβ := LazyQuarticParameters.beta_square p hp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  unfold radius condition decrease
  rw [div_pow, Real.sq_sqrt hp.2.1.le]
  field_simp [ha.ne', hb.ne', hp.1.ne']
  nlinarith only [congrArg (fun z : ℝ => p.Δ * z) hβ]

lemma charge_bound (p : Params) (hp : spec.valid p) :
    4 * chargeCoefficient p * p.Δ / radius p ≤ 2 ^ 23 * condition p ^ (3 / 2 : ℝ) := by
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hb := LazyQuarticParameters.beta_pos p hp
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hr := LazyQuarticParameters.radius_pos p hp
  have hΔ := hp.2.1
  have hk : 0 < condition p := div_pos hb ha
  have hroot : 0 < Real.sqrt (alpha p / (64 * beta p) * decrease p) := by positivity
  have hi := metric_charge_identity p hp
  have hpow : (condition p ^ (3 / 2 : ℝ)) ^ 2 = condition p ^ 3 := by
    rw [← Real.rpow_mul_natCast hk.le]
    norm_num
  have hsq : (64 * p.Δ) ^ 2 ≤
      (2 ^ 23 * condition p ^ (3 / 2 : ℝ) * (radius p * Real.sqrt (alpha p / (64 * beta p) * decrease p))) ^ 2 := by
    simp only [mul_pow, hpow]
    nlinarith only [hi, sq_nonneg p.Δ]
  have hh := (sq_le_sq₀ (show 0 ≤ 64 * p.Δ by positivity) (by positivity)).mp hsq
  unfold chargeCoefficient
  apply (div_le_iff₀ hr).mpr
  calc
    _ = 64 * p.Δ / Real.sqrt (alpha p / (64 * beta p) * decrease p) := by ring
    _ ≤ _ := (div_le_iff₀ hroot).mpr (by nlinarith only [hh])

lemma hessian_bound (p : Params) (hp : spec.valid p) {n : ℕ}
    (hn : (n : ℝ) ≤ 4 * chargeCoefficient p * p.Δ / radius p) :
    n + 1 ≤ ⌈2 ^ 62 * (1 + p.Δ ^ (3 / 4 : ℝ) * p.L₃ ^ (1 / 4 : ℝ) / p.ε)⌉₊ := by
  have hΔ := hp.2.1
  have hL := hp.1
  have hε := hp.2.2.2
  have hh := hn.trans (charge_bound p hp)
  have hk := LazyQuarticRates.condition_power p hp (r := (3 / 2 : ℝ))
  norm_num at hk
  have hnon : 0 ≤ p.Δ ^ (3 / 4 : ℝ) * p.L₃ ^ (1 / 4 : ℝ) / p.ε := by positivity
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans ?_ (Nat.le_ceil _)
  push_cast
  norm_num at hh ⊢
  nlinarith only [hh, hk, hnon]

end LongTails.Proofs.LazyQuarticHessianBudget
