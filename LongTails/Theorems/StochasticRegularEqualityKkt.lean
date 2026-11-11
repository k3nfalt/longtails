import LongTails.Setups.StochasticRegularEqualities
import LongTails.Proofs.StochasticEqualityAmplification
import LongTails.Proofs.StochasticEqualityCost

namespace LongTails.Theorems.StochasticRegularEqualityKkt

open OracleTemplate
open LongTails.Setups.StochasticRegularEqualities

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈10 ^ 47 * ((((2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise) ^ 38 + (2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise) ^ 48 * p.σ ^ 2 + (2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise) ^ 60 * p.σ / p.ε) * (1 + Real.log ((2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise) / p.ε)) + (2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise) ^ 14 * p.σ ^ 2 * (1 + Real.log ((2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise) / p.ε)) ^ 2) / p.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.StochasticRegularEqualities.spec budget := by
  refine ⟨LongTails.Algorithms.StochasticEquality.algorithm, ?_, ?_⟩
  · intro p hp I O hI
    exact LongTails.Proofs.StochasticEqualityAmplification.admissible_execution p hp I O hI
      (budget p 0) (by
        simpa only [budget, LongTails.Proofs.StochasticEqualityTuning.scale] using
          LongTails.Proofs.StochasticEqualityCost.calls_le_ceiling p hp)
  · intro p hp
    trivial

end LongTails.Theorems.StochasticRegularEqualityKkt
