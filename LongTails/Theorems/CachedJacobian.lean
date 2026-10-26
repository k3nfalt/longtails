import LongTails.Setups.LipschitzJacobianMonotone
import LongTails.Algorithms.CachedJacobian
import LongTails.Proofs.CachedJacobianBudget

namespace LongTails.Theorems.CachedJacobian

open OracleTemplate MeasureTheory
open LongTails.Setups.LipschitzJacobianMonotone
open LongTails.Algorithms.CachedJacobian
open LongTails.Proofs

noncomputable def budget : (let S := LongTails.Setups.LipschitzJacobianMonotone.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 0 then ⌈100000 * (1 + Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε)) * (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε))⌉₊ else ⌈20000 * (1 + Real.sqrt (p.L * p.D ^ 2 / (p.m * p.ε))) * (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε))⌉₊

theorem result : Convergence LongTails.Setups.LipschitzJacobianMonotone.spec budget := by
  refine ⟨output, ?_, fun _ _ => trivial⟩
  intro p hv F O hO
  obtain ⟨hF, hmono, hJ, hvalue, hderiv⟩ := hO
  have hanswer : ∀ k q seed, O.answer k q seed = CachedJacobianExecution.replies p F q := by
    rintro k ⟨i, x⟩ seed
    fin_cases i
    · simpa [CachedJacobianExecution.replies] using hvalue k x seed
    · simpa [CachedJacobianExecution.replies] using hderiv k x seed
  have hb (i : Fin 2) : EnergyHessianExecution.counts
      (CachedJacobianExecution.replies p F) (plan p) i ≤ budget p i :=
    CachedJacobianBudget.counts_sufficient hv hF hmono hJ i
  apply Filter.Eventually.of_forall
  intro seed
  change execute O (output p) (budget p) seed.1 seed.2 ∈ p.X ∧ _
  simp only [output]
  rw [EnergyHessianExecution.execute_of_counts (CachedJacobianExecution.replies p F)
    (0, p.x0) p.x0 (plan p) O (budget p) hanswer hb seed.1 seed.2,
    CachedJacobianCounts.plan_eval]
  have hc := CachedJacobianConvergence.trajectory_correct hv hF hmono (outerCount p)
  exact ⟨hc.point_mem, (CachedJacobianConvergence.trajectory p F (outerCount p)).normal,
    hc.normal_mem, CachedJacobianConvergence.final_residual hv hF hmono hJ⟩

end LongTails.Theorems.CachedJacobian
