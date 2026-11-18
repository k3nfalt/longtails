import LongTails.Setups.EuclideanWeakMinty
import LongTails.Proofs.EuclideanWeakMintyExtragradientRun

namespace LongTails.Theorems.EuclideanWeakMintyExtragradient

open OracleTemplate LongTails.Algorithms.EuclideanWeakMintyExtragradient

noncomputable def budget : (let S := LongTails.Setups.EuclideanWeakMinty.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.EuclideanWeakMinty.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp F O had
  exact LongTails.Proofs.EuclideanWeakMintyExtragradientRun.success p hp F O had

end LongTails.Theorems.EuclideanWeakMintyExtragradient
