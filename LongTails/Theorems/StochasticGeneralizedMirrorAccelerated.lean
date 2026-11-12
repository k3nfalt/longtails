import LongTails.Setups.StochasticGeneralizedMirror
import LongTails.Algorithms.StochasticGeneralizedMirror
import LongTails.Proofs.GeneralizedMirrorConvergence

open OracleTemplate
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror

namespace LongTails.Theorems.StochasticGeneralizedMirrorAccelerated

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈8589934592 * (1 + (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) + Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (256 : ℝ) ^ (1 / (q.α - 1)) * (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) * (Real.log (8589934592 * (1 + (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) + Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (256 : ℝ) ^ (1 / (q.α - 1)) * (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) / q.δ)) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.StochasticGeneralizedMirror.spec budget := by
  refine ⟨fun q => ?_, ?_, fun _ _ => trivial⟩
  · let Λ := 96 * q.σ + q.ε / q.R + 2 * (256 * q.σ ^ q.α * q.R / q.ε) ^ (1 / (q.α - 1))
    let V := 4 * Λ ^ (2 - q.α) * q.σ ^ q.α
    let H := 4096 * (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) + 1024 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + 262144 * (1 + Λ * q.R / q.ε + V * q.R ^ 2 / q.ε ^ 2)
    let ell := Real.log (64 * H / q.δ)
    exact algorithm q ell ⌈8 * ell⌉₊
  · intro q hq I O hI
    have hc := LongTails.Proofs.GeneralizedMirrorBudget.explicit_calls_bound q hq
    have hb : ⌈LongTails.Proofs.GeneralizedMirrorWeights.horizonScale q *
        LongTails.Proofs.GeneralizedMirrorBudget.confidence
          (LongTails.Proofs.GeneralizedMirrorWeights.horizonScale q) q.δ⌉₊ *
        (⌈8 * LongTails.Proofs.GeneralizedMirrorBudget.confidence
          (LongTails.Proofs.GeneralizedMirrorWeights.horizonScale q) q.δ⌉₊ + 2) ≤ budget q 0 := by
      simpa only [budget, LongTails.Proofs.GeneralizedMirrorBudget.rateScale] using hc
    exact LongTails.Proofs.GeneralizedMirrorConvergence.execution_success q hq I O hI (budget q 0) hb

end LongTails.Theorems.StochasticGeneralizedMirrorAccelerated
