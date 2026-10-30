import LongTails.Setups.NonsmoothHiddenConvex
import LongTails.Proofs.NonsmoothHiddenConvergence

namespace OracleTemplate.NonsmoothHidden

noncomputable def budget : (let S := LongTails.Setups.NonsmoothHiddenConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈10000000000 * ((1 + 64 * p.LJ * p.R / p.μ) * (p.Lc / p.μ + p.G ^ 2 * p.Lc ^ 3 * p.R ^ 2 / (p.μ ^ 3 * p.ε ^ 2))) * Real.log (10000000000 * (2 + (1 + 64 * p.LJ * p.R / p.μ) * (p.Lc / p.μ + p.G ^ 2 * p.Lc ^ 3 * p.R ^ 2 / (p.μ ^ 3 * p.ε ^ 2)))) ^ 3⌉₊

theorem result : Convergence LongTails.Setups.NonsmoothHiddenConvex.spec budget := by
  refine ⟨tunedAlgorithm, ?_, fun _ _ => trivial⟩
  intro p hp I O had
  have hw := parameter_work p hp
  have hb : ((outerIterations p * localIterations p : ℕ) : ℝ) ≤ (budget p 0 : ℝ) := by
    rw [Nat.cast_mul]
    have hh := hw.trans (Nat.le_ceil _)
    simpa only [budget, workSize, shape, conditioning] using hh
  have hB : outerIterations p * localIterations p ≤ budget p 0 := by exact_mod_cast hb
  exact execution_success p hp I O had (budget p 0) hB

end OracleTemplate.NonsmoothHidden
