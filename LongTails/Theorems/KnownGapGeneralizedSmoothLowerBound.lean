import LongTails.TemplateLowerBound
import LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
import LongTails.Proofs.KnownGapChainLowerBound
import LongTails.Proofs.KnownGapAccuracyInstance

namespace LongTails.Theorems.KnownGapGeneralizedSmoothLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊max (Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 8192) (min ((p.L1 * p.R * Real.log (p.Δ / p.ε)) ^ (2 / 3 : ℝ)) (p.L1 * p.R) / (2048 * Real.log (2 + p.L1 * p.R)))⌋₊

theorem result : NonConvergence LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension.spec budget := by
  intro p hp A _ b hb
  have hN : b 0 ≤ ⌊max (Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 8192)
      (LongTails.Proofs.KnownGapParameters.X p)⌋₊ := hb 0
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  by_cases hX : b 0 ≤ ⌊LongTails.Proofs.KnownGapParameters.X p⌋₊
  · exact LongTails.Proofs.KnownGapChainLowerBound.exists_failure p hp (b 0) (by
      change b 0 + 1 ≤ ⌊LongTails.Proofs.KnownGapParameters.X p⌋₊ + 1
      exact Nat.add_le_add_right hX 1) A
  · refine LongTails.Proofs.KnownGapAccuracyInstance.exists_failure p hp (b 0) ?_ A
    have hpos : 1 ≤ b 0 := by omega
    have hmax : b 0 ≤ ⌊Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 8192⌋₊ := by
      rcases le_total (Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 8192)
          (LongTails.Proofs.KnownGapParameters.X p) with h | h
      · rw [max_eq_right h] at hN
        exact absurd hN hX
      · rwa [max_eq_left h] at hN
    have h0 : 0 ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 8192 := by positivity
    have hfl : (b 0 : ℝ) ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 8192 := (Nat.le_floor_iff h0).mp hmax
    have h1 : (1 : ℝ) ≤ b 0 := by exact_mod_cast hpos
    linarith

end LongTails.Theorems.KnownGapGeneralizedSmoothLowerBound
