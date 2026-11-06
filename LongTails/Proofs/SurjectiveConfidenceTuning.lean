import LongTails.Algorithms.SurjectiveConfidence
import LongTails.Proofs.SurjectiveConfidenceSelection

namespace LongTails.Proofs.SurjectiveConfidenceTuning

open LongTails.Algorithms.SurjectiveConfidence
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Setups.ConfidentStochasticSurjectiveInequalities

lemma batch_sufficient (p : Params) (hp : spec.valid p) :
    144 * p.problem.σ ^ 2 ≤ (batch p : ℝ) * (certificateError p.problem / 4) ^ 2 := by
  have hm : (p.problem.m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.1.1).ne'
  have hH : p.problem.H ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.1.2.1).ne'
  have he : p.problem.ε ≠ 0 := hp.1.2.2.2.2.1.ne'
  have hb : 2 ^ 40 * (p.problem.m : ℝ) ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2 /
      p.problem.ε ^ 2 ≤ (batch p : ℝ) := by
    unfold batch
    have h := Nat.le_ceil (2 ^ 40 * (p.problem.m : ℝ) ^ 4 * p.problem.H ^ 18 *
      p.problem.σ ^ 2 / p.problem.ε ^ 2)
    push_cast
    linarith
  have hid : (2 ^ 40 * (p.problem.m : ℝ) ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2 /
      p.problem.ε ^ 2) * (certificateError p.problem / 4) ^ 2 = 256 * p.problem.σ ^ 2 := by
    unfold certificateError
    field_simp [hm, hH, he]
    ring
  have h := mul_le_mul_of_nonneg_right hb (sq_nonneg (certificateError p.problem / 4))
  rw [hid] at h
  nlinarith [sq_nonneg p.problem.σ]

lemma half_power_log_bound {a : ℝ} (ha : 1 ≤ a) {n : ℕ}
    (hn : 2 * Real.log a ≤ (n : ℝ)) : (1 / 2 : ℝ) ^ n ≤ 1 / a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
    linarith
  have hlog0 : 0 ≤ Real.log a := Real.log_nonneg ha
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hexp : (1 / 2 : ℝ) ^ n = Real.exp (-(n : ℝ) * Real.log 2) := by
    rw [show -(n : ℝ) * Real.log 2 = (n : ℝ) * (-Real.log 2) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  rw [hexp, show 1 / a = Real.exp (-Real.log a) by rw [Real.exp_neg, Real.exp_log ha0]; simp only [one_div]]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma confidence_failure_bound (p : Params) (hp : spec.valid p) :
    (1 / 2 : ℝ) ^ replicas p + (replicas p : ℝ) * (1 / 2 : ℝ) ^ groups p ≤ p.δ := by
  have hd := hp.2.1
  have hd1 := hp.2.2
  have ha : 1 ≤ 2 / p.δ := (le_div_iff₀ hd).mpr (by linarith)
  have hR : 2 * Real.log (2 / p.δ) ≤ (replicas p : ℝ) := by
    unfold replicas
    have h := Nat.le_ceil (2 * Real.log (2 / p.δ))
    push_cast
    linarith
  have hRf := half_power_log_bound ha hR
  have hid : 1 / (2 / p.δ) = p.δ / 2 := by field_simp
  rw [hid] at hRf
  have hlog := Real.log_nonneg ha
  have hRupper : (replicas p : ℝ) ≤ 4 / p.δ := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (2 / p.δ) by positivity)
    have hln := Real.log_le_sub_one_of_pos (show 0 < 2 / p.δ by positivity)
    unfold replicas
    push_cast
    rw [show (4 : ℝ) / p.δ = 2 * (2 / p.δ) by ring]
    linarith
  have hak : 1 ≤ (2 / p.δ) ^ 4 := one_le_pow₀ ha
  have hk : 2 * Real.log ((2 / p.δ) ^ 4) ≤ (groups p : ℝ) := by
    rw [Real.log_pow]
    unfold groups
    have h := Nat.le_ceil (8 * Real.log (2 / p.δ))
    push_cast
    nlinarith
  have hkf := half_power_log_bound hak hk
  have hkId : 1 / (2 / p.δ) ^ 4 = p.δ ^ 4 / 16 := by field_simp; ring
  rw [hkId] at hkf
  have hprod := mul_le_mul hRupper hkf (by positivity) (by positivity)
  have hprodId : 4 / p.δ * (p.δ ^ 4 / 16) = p.δ ^ 3 / 4 := by field_simp; ring
  rw [hprodId] at hprod
  have hd3 : p.δ ^ 3 ≤ p.δ := by
    have hsq : p.δ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  linarith

end LongTails.Proofs.SurjectiveConfidenceTuning
