import LongTails.TemplateLowerBound
import LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
import LongTails.Proofs.InterpolatedFiniteSumCombinedLower

namespace LongTails.Theorems.ExpectedInterpolatedGeneralizedFiniteSumLowerBound

open OracleTemplate LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

noncomputable def budget : (let S := LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊((p.n : ℝ) + Real.sqrt (p.n * p.L0 * p.R ^ 2 / p.ε) + Real.sqrt p.n * p.L1 * p.R + p.n * (p.L1 * p.R) ^ (2 / 3 : ℝ)) / (1000000000 * (1 + Real.log (2 + p.n + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε)) ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec budget := by
  intro p hp A _ b hb
  have he : b = fun _ => b 0 := by funext i; exact congrArg b (Subsingleton.elim i 0)
  rw [he]
  apply LongTails.Proofs.InterpolatedFiniteSumCombinedLower.combined_failure p hp A (b 0)
  have hL0 := hp.1
  have hL1 := hp.2.1
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg hL1 hR.le
  have hnonneg : 0 ≤ ((p.n : ℝ) + Real.sqrt (p.n * p.L0 * p.R ^ 2 / p.ε) +
      Real.sqrt p.n * p.L1 * p.R + p.n * (p.L1 * p.R) ^ (2 / 3 : ℝ)) /
      (1000000000 * (1 + Real.log (2 + p.n + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε)) ^ 2) := by positivity
  have hcast : (b 0 : ℝ) ≤ budget p 0 := by exact_mod_cast hb 0
  have hh := hcast.trans (Nat.floor_le hnonneg)
  have hs : (p.n : ℝ) * p.L0 * p.R ^ 2 / p.ε = p.n * (p.L0 * p.R ^ 2 / p.ε) := by ring
  have hx : Real.sqrt p.n * p.L1 * p.R = Real.sqrt p.n * (p.L1 * p.R) := by ring
  rw [hs, hx] at hh
  exact hh

end LongTails.Theorems.ExpectedInterpolatedGeneralizedFiniteSumLowerBound
