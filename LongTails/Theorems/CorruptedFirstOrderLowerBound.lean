import LongTails.Setups.CorruptedFirstOrderNonconvex.HighDimensional
import LongTails.Proofs.CorruptedFirstOrderLowerBound

open OracleTemplate LongTails.Setups.CorruptedFirstOrderNonconvex

namespace LongTails.Theorems.CorruptedFirstOrderLowerBound

noncomputable def budget : (let S := LongTails.Setups.CorruptedFirstOrderNonconvex.HighDimensional.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.k + ⌊p.L * p.Δ / (2 ^ 25 * p.ε ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.CorruptedFirstOrderNonconvex.HighDimensional.spec budget := by
  intro p hp A _ b hb
  have heq : b = fun _ => b 0 := by funext i; rw [Subsingleton.elim i 0]
  let N := b 0
  have heq' : b = fun _ => N := heq
  rw [heq']
  exact LongTails.Proofs.CorruptedFirstOrderLowerBound.adversary p hp A N (hb 0)

end LongTails.Theorems.CorruptedFirstOrderLowerBound
