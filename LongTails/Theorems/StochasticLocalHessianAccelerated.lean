import LongTails.Setups.StochasticLocalHessianConvex
import LongTails.Proofs.NoisyNewtonConvergence

namespace LongTails.Theorems.StochasticLocalHessianAccelerated

open OracleTemplate
open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonTuning

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p ch => ⌈2 ^ 80 * (1 + (p.M₁ * p.R ^ 2) ^ (1 / 3 : ℝ) + (p.R / p.ρ) ^ (2 / 3 : ℝ) + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) + Real.sqrt (p.δ * p.R ^ 2 / p.ε) + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) * Real.log (2 + p.Δ / p.ε + p.δ * p.R ^ 2 / p.ε + p.M₀ * p.R ^ 3 / p.ε + p.M₁ * p.R ^ 2 + (p.R / p.ρ) ^ 2 + 1 / p.β + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) ^ 3⌉₊

theorem result : Convergence LongTails.Setups.StochasticLocalHessianConvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I O ha
  apply LongTails.Proofs.NoisyNewtonConvergence.admissible_success p hp I O ha
  intro ch
  simpa only [budget, shape, scaleBase, show (2 : ℝ) ^ 80 = 1208925819614629174706176 by norm_num]
    using (Nat.le_ceil (1208925819614629174706176 *
      (shape p + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) *
      Real.log (scaleBase p) ^ 3))

end LongTails.Theorems.StochasticLocalHessianAccelerated
