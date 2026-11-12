import LongTails.TemplateLowerBound
import LongTails.Setups.SmoothAndConvexExpected
import LongTails.Proofs.SmoothConvexFiniteLowerBound

namespace LongTails.Theorems.SmoothConvexExpectedLowerBound

open OracleTemplate LongTails.Proofs.SmoothConvexFiniteLowerBound
open LongTails.Proofs.SmoothConvexFiniteExpectation

noncomputable def budget : (let S := LongTails.Setups.SmoothAndConvexExpected.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊Real.sqrt (q.L * q.R ^ 2 / q.ε) / 512⌋₊

theorem result : NonConvergence LongTails.Setups.SmoothAndConvexExpected.spec budget := by
  intro q h A _ b hb
  obtain ⟨hL, hR, hε, hregime, hd⟩ := h
  have hN := hb 0
  have hdN : 65536 * (b 0 + 1) ^ 5 ≤ q.d := by
    apply le_trans _ hd
    change 65536 * (b 0 + 1) ^ 5 ≤ 65536 * (budget q 0 + 1) ^ 5
    gcongr
  have hgap := floor_budget_insufficient q.L q.R q.ε hL hR hε hregime
  have hgapN : 16384 * ((b 0 : ℝ) + 1) ^ 2 * q.ε < q.L * q.R ^ 2 := by
    apply lt_of_le_of_lt _ hgap
    change 16384 * ((b 0 : ℝ) + 1) ^ 2 * q.ε ≤
      16384 * ((budget q 0 : ℝ) + 1) ^ 2 * q.ε
    gcongr
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact exists_failure q (b 0) hL hR hdN hgapN A

end LongTails.Theorems.SmoothConvexExpectedLowerBound
