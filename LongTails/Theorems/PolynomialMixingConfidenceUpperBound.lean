import LongTails.Setups.PolynomialMixingSubgradient
import LongTails.Proofs.PolynomialMixingConvergence

namespace LongTails.Theorems.PolynomialMixingConfidenceUpperBound

open OracleTemplate LongTails.Setups.PolynomialMixingSubgradient
open LongTails.Algorithms.PolynomialMixingSelection LongTails.Proofs.PolynomialMixingBudget
open LongTails.Proofs.PolynomialMixingConvergence

noncomputable def budget : (let S := LongTails.Setups.PolynomialMixingSubgradient.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈q.τ * (32 * Real.log (8 / q.δ)) ^ 2 * (((2 : ℝ) ^ 24 * q.G * q.R / q.ε) ^ (q.p / (q.p - 1) * (1 + 1 / q.β)) + ((32 * Real.log (8 / q.δ)) ^ 2 / q.δ) ^ (1 / q.β))⌉₊

theorem result : Convergence LongTails.Setups.PolynomialMixingSubgradient.spec budget := by
  refine ⟨method, ?_, fun _ _ => trivial⟩
  intro q hp f O h
  have hK : LongTails.Proofs.PolynomialMixingExecution.cost (schedule q) ≤ budget q 0 := by
    unfold budget
    rw [show (2 : ℝ) ^ 24 = 16777216 by norm_num]
    exact_mod_cast (cost_bound q hp).trans (Nat.le_ceil _)
  exact success q hp f O h (budget q 0) hK

end LongTails.Theorems.PolynomialMixingConfidenceUpperBound
