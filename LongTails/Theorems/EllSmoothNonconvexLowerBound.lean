import LongTails.Setups.HighDimensionalEllSmoothNonconvex
import LongTails.Proofs.EllSmoothLowerBound

open OracleTemplate LongTails.Setups.EllSmoothNonconvex

namespace LongTails.Theorems.EllSmoothNonconvexLowerBound

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalEllSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalEllSmoothNonconvex.spec budget := by
  intro p hp A _ b hb
  have heq : b = fun _ => b 0 := by funext i; rw [Subsingleton.elim i 0]
  let N := b 0
  have heq' : b = fun _ => N := heq
  rw [heq']
  exact LongTails.Proofs.EllSmoothLowerBound.exists_failure p hp A N (hb 0)

end LongTails.Theorems.EllSmoothNonconvexLowerBound
