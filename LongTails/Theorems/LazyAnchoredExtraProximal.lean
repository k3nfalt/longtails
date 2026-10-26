import LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
import LongTails.Proofs.LazyAnchoredExecution
import LongTails.Proofs.LazyAnchoredBudget

namespace LongTails.Theorems.LazyAnchoredExtraProximal

open OracleTemplate MeasureTheory
open LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
open LongTails.Algorithms.LazyAnchoredExtraProximal
open LongTails.Proofs.LazyAnchoredInner
open LongTails.Proofs.LazyAnchoredOuter
open LongTails.Proofs.LazyAnchoredExecution
open LongTails.Proofs.LazyAnchoredBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 1 then ⌈(p.L * p.D ^ 2 / (p.m * p.ε)) ^ (2 / 5 : ℝ)⌉₊ + 1 else 2 ^ 15 * (p.m + 1) * (⌈(p.L * p.D ^ 2 / (p.m * p.ε)) ^ (2 / 5 : ℝ)⌉₊ + 1) * (Nat.log2 (p.m * (⌈(p.L * p.D ^ 2 / (p.m * p.ε)) ^ (2 / 5 : ℝ)⌉₊ + 1)) + 1) ^ 2

theorem result : Convergence LongTails.Setups.UnconstrainedLipschitzJacobianMonotone.spec budget := by
  refine ⟨fun p => algorithm (p := p), ?_, fun _ _ => trivial⟩
  intro p hp F O hadm
  have hreg := regular_of_admissible p hp F O hadm
  have hpp : 0 < p.D ∧ 0 < p.ε := ⟨hp.2.1, hp.2.2.1⟩
  obtain ⟨xs, hxs, hD⟩ := hadm.2.2.2.2.2
  apply Filter.Eventually.of_forall
  rintro ⟨seed, ξ⟩
  change ‖F (execute O algorithm (budget p) seed ξ)‖ ≤ p.ε
  rw [execution_output p hp F O hadm (budget p) (by simp [budget, outerCount])
    (by simpa [budget, outerCount, Nat.log2_eq_log_two] using ticks_budget F hreg hpp hp.2.2.2 hxs hD) seed ξ]
  exact final_accuracy F hreg hpp hxs hD

end LongTails.Theorems.LazyAnchoredExtraProximal
