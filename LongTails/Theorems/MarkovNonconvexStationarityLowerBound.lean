import LongTails.TemplateLowerBound
import LongTails.Setups.MarkovSmoothNonconvex
import LongTails.Proofs.MarkovParityLower

namespace LongTails.Theorems.MarkovNonconvexStationarityLowerBound

open OracleTemplate LongTails.Proofs.MarkovParityLower LongTails.Proofs.MarkovParityOracle
open LongTails.Proofs.AbcHardOracle LongTails.Setups.MarkovSmoothNonconvex

noncomputable def budget : (let S := LongTails.Setups.MarkovSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊p.τ * p.L * p.Δ * p.σ ^ 2 / (2 ^ 56 * p.ε ^ 4)⌋₊

theorem result : NonConvergence LongTails.Setups.MarkovSmoothNonconvex.spec budget := by
  intro p hv A _ b hb
  obtain ⟨π, hπ⟩ := exists_failure p hv A (b 0) (hb 0)
  refine ⟨objective (scale p hv) π p.x0, oracle p hv π, admissible p hv π, ?_⟩
  have he : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [he]
  exact hπ

end LongTails.Theorems.MarkovNonconvexStationarityLowerBound
