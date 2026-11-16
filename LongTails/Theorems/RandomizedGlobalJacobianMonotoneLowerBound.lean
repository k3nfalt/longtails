import LongTails.TemplateLowerBound
import LongTails.Setups.GlobalJacobianMonotoneExpected
import LongTails.Proofs.LocalizedMonotoneLowerBound
import LongTails.Proofs.LocalizedMonotoneBudget

namespace LongTails.Theorems.RandomizedGlobalJacobianMonotoneLowerBound

open OracleTemplate LongTails.Proofs.LocalizedMonotoneLowerBound
open LongTails.Proofs.LocalizedMonotoneBudget

noncomputable def budget : (let S := LongTails.Setups.GlobalJacobianMonotoneExpected.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(p.L * p.R ^ 2 / (4096 * p.ε)) ^ (2 / 5 : ℝ)⌋₊

theorem result : NonConvergence LongTails.Setups.GlobalJacobianMonotoneExpected.spec budget := by
  intro p hp A _ b hb
  obtain ⟨hL, hR, hε, hregime, hd⟩ := hp
  let N := budget p 0
  have hk : b 0 ≤ N + 1 := (hb 0).trans (Nat.le_succ N)
  have hdim : 4096 * (N + 1 + 1) ^ 5 ≤ p.d := by
    simpa only [N, budget, Nat.add_assoc] using hd
  have hgap : 2 * p.ε < p.L * p.R ^ 2 /
      (32 * (((N + 1 : ℕ) : ℝ) + 1) ^ 2 * Real.sqrt (((N + 1 : ℕ) : ℝ) + 1)) := by
    simpa only [N, budget, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      floor_budget_residual p.L p.R p.ε hL hR hε hregime
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact exists_failure p (N + 1) (b 0) hL hR (by omega) hk hdim hgap A

end LongTails.Theorems.RandomizedGlobalJacobianMonotoneLowerBound
