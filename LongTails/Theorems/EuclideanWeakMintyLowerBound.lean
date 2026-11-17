import LongTails.TemplateLowerBound
import LongTails.Setups.EuclideanWeakMinty
import LongTails.Proofs.MintyChainLowerBound

namespace LongTails.Theorems.EuclideanWeakMintyLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.EuclideanWeakMinty.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊min ((p.L * p.R / (28 * p.ε)) ^ 2) (((p.d : ℝ) / 257) ^ ((1 : ℝ) / 3))⌋₊ - 1

theorem result : NonConvergence LongTails.Setups.EuclideanWeakMinty.spec budget := by
  intro p hp A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact LongTails.Proofs.MintyChainLowerBound.exists_failure p hp (b 0) (hb 0) A

end LongTails.Theorems.EuclideanWeakMintyLowerBound
