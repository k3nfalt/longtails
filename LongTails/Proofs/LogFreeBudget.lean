import LongTails.Proofs.LogFreeExecution

namespace LongTails.Proofs.LogFreeBudget

open OracleTemplate LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LogFreeProxNewton
open LongTails.Proofs.LogFreeExecution LongTails.Proofs.EnergyHessianExecution
  LongTails.Proofs.LogFreeParameters

variable (p : Params)

lemma plan_budget (hp : spec.valid p) (g : Fin 2 × p.E → Reply p.E) (i : Fin 2) :
    counts g (plan p) i ≤ ⌈2 ^ 30 * (1 + p.Δ * p.L₃ ^ (1 / 3 : ℝ) / p.ε ^ (4 / 3 : ℝ) +
      Real.log (2 + p.H₀ * p.Δ / p.ε ^ 2 + p.L₃ * p.Δ ^ 3 / p.ε ^ 4))⌉₊ := by
  rw [plan_counts]
  have hX : (1 : ℝ) ≤ 1 + complexity p + Real.log (logArgument p) := by
    have hS0 : 0 ≤ complexity p := by
      rw [complexity_eq p hp]; exact div_nonneg hp.2.1.le (unit_pos p hp).le
    have hΓ := logArgument_ge p hp
    have : 0 ≤ Real.log (logArgument p) := Real.log_nonneg (by linarith)
    linarith
  have hN : (steps p : ℝ) ≤ 2 ^ 27 * (1 + complexity p + Real.log (logArgument p)) + 1 := by
    unfold steps
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 27 * (1 + complexity p + Real.log (logArgument p)) by
      positivity)
    linarith
  have hc : (1 + (if i = 0 then 6 else 2) * steps p : ℕ) ≤ (1 + 6 * steps p : ℕ) := by
    split_ifs <;> omega
  refine hc.trans ?_
  apply (Nat.cast_le (α := ℝ)).mp
  refine le_trans ?_ (Nat.le_ceil _)
  push_cast
  change (1 : ℝ) + 6 * steps p ≤ 2 ^ 30 * (1 + complexity p + Real.log (logArgument p))
  nlinarith

end LongTails.Proofs.LogFreeBudget
