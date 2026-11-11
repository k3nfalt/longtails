import LongTails.TemplateLowerBound
import LongTails.Setups.SmoothAndConvexExpected
import LongTails.Proofs.SmoothConvexFiniteLowerBound

namespace LongTails.LowerBounds.SmoothAndConvexExpected

open OracleTemplate LongTails.Proofs.SmoothConvexFiniteLowerBound
open LongTails.Proofs.SmoothConvexFiniteExpectation

noncomputable def budget : (let S := LongTails.Setups.SmoothAndConvexExpected.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊Real.sqrt (q.L * q.R ^ 2 / q.ε) / 512⌋₊

theorem result : NonConvergence LongTails.Setups.SmoothAndConvexExpected.spec budget := by
  intro q h A _
  obtain ⟨hL, hR, hε, hregime, hd⟩ := h
  exact exists_failure q (budget q 0) hL hR hd
    (floor_budget_insufficient q.L q.R q.ε hL hR hε hregime) A

end LongTails.LowerBounds.SmoothAndConvexExpected
