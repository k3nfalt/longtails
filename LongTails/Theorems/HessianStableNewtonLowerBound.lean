import LongTails.Setups.HighDimensionalHessianStableSkewMonotone
import LongTails.TemplateLowerBound
import LongTails.Proofs.HsLowerBound

namespace LongTails.Theorems.HessianStableNewtonLowerBound

open OracleTemplate MeasureTheory
open LongTails.Setups.HighDimensionalHessianStableSkewMonotone
open LongTails.Proofs.HsLowerBound

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(p.M * p.D / (2 ^ 18 * Real.log (2 + p.M * p.D))) ^ ((2 : ℝ) / 3)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalHessianStableSkewMonotone.spec budget := by
  intro P hv A _ b hb
  obtain ⟨π, hπ⟩ := hard_failure A hv b hb
  exact ⟨hardF P π, hardOracle P π, hard_admissible π hv, hπ⟩

end LongTails.Theorems.HessianStableNewtonLowerBound
