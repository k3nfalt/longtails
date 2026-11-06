import LongTails.Proofs.SurjectiveConfidenceTuning
import LongTails.Proofs.SurjectiveProxLinearBudget

namespace LongTails.Proofs.SurjectiveConfidenceBudget

open LongTails.Setups.ConfidentStochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveConfidence

lemma total_call_budget (p : Params) (hp : spec.valid p) :
    trialCalls p * replicas p ≤
      ⌈(2 * Real.log (2 / p.δ) + 2) * (70 +
        (2 ^ 29 * p.problem.m ^ 2 * p.problem.H ^ 10 * p.problem.Δ +
          2 ^ 44 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2) / p.problem.ε ^ 2 +
        2 ^ 48 * p.problem.m ^ 4 * p.problem.H ^ 19 * p.problem.Δ * p.problem.σ / p.problem.ε ^ 3 +
        (8 * Real.log (2 / p.δ) + 2) *
          (2 + 2 ^ 40 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2 / p.problem.ε ^ 2))⌉₊ := by
  have hd := hp.2.1
  have hδ := hp.2.2
  have hlog : 0 ≤ Real.log (2 / p.δ) :=
    Real.log_nonneg ((le_div_iff₀ hd).mpr (by linarith))
  have hH : 0 ≤ p.problem.H := le_trans zero_le_one hp.1.2.1
  have he := hp.1.2.2.2.2.1
  have hσ := hp.1.2.2.1
  have hΔ := hp.1.2.2.2.1
  have hR : (replicas p : ℝ) ≤ 2 * Real.log (2 / p.δ) + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (2 / p.δ) by positivity)
    unfold replicas
    push_cast
    linarith
  have hk : (groups p : ℝ) ≤ 8 * Real.log (2 / p.δ) + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 8 * Real.log (2 / p.δ) by positivity)
    unfold groups
    push_cast
    linarith
  have hb : (batch p : ℝ) ≤ 2 + 2 ^ 40 * p.problem.m ^ 4 * p.problem.H ^ 18 *
      p.problem.σ ^ 2 / p.problem.ε ^ 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 40 * (p.problem.m : ℝ) ^ 4 *
      p.problem.H ^ 18 * p.problem.σ ^ 2 / p.problem.ε ^ 2 by positivity)
    unfold batch
    push_cast
    linarith
  have hT : (trainingCalls p : ℝ) ≤ 70 +
      (2 ^ 29 * p.problem.m ^ 2 * p.problem.H ^ 10 * p.problem.Δ +
        2 ^ 44 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2) / p.problem.ε ^ 2 +
      2 ^ 48 * p.problem.m ^ 4 * p.problem.H ^ 19 * p.problem.Δ * p.problem.σ / p.problem.ε ^ 3 := by
    have h := SurjectiveProxLinearBudget.total_call_budget p.problem hp.1
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 69 +
      (2 ^ 29 * (p.problem.m : ℝ) ^ 2 * p.problem.H ^ 10 * p.problem.Δ +
        2 ^ 44 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2) / p.problem.ε ^ 2 +
      2 ^ 48 * p.problem.m ^ 4 * p.problem.H ^ 19 * p.problem.Δ * p.problem.σ / p.problem.ε ^ 3 by positivity)
    have hh := (Nat.cast_le (α := ℝ)).mpr h
    change (trainingCalls p : ℝ) ≤ _ at hh
    linarith
  have hkb := mul_le_mul hk hb (Nat.cast_nonneg _) (by positivity)
  have hL := add_le_add hT hkb
  have htotal := mul_le_mul hR hL (by positivity) (by positivity)
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans _ (Nat.le_ceil _)
  convert htotal using 1
  push_cast [trialCalls]
  ring

end LongTails.Proofs.SurjectiveConfidenceBudget
