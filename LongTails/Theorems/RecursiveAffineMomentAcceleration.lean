import LongTails.Setups.AffineMomentConvex
import LongTails.Proofs.StochasticEnvelopeRun
import LongTails.Proofs.StochasticEnvelopeBudget

namespace LongTails.Theorems.RecursiveAffineMomentAcceleration

open OracleTemplate LongTails.Setups.AffineMomentConvex
open LongTails.Algorithms.StochasticEnvelope

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈Real.exp ((2 : ℝ) ^ (32 : ℕ) * (p.α / (p.α - 1)) ^ 4 * (1 + Real.sqrt (Real.log (4 + p.L * p.R ^ 2 / p.ε + (p.σ0 * p.R / p.ε) ^ (p.α / (p.α - 1)) + 1 / p.δ))) * Real.log (2 + p.α / (p.α - 1) + Real.log (4 + p.L * p.R ^ 2 / p.ε + (p.σ0 * p.R / p.ε) ^ (p.α / (p.α - 1)) + 1 / p.δ))) * ((1 + p.σ) ^ (p.α / (p.α - 1)) * Real.sqrt (p.L * p.R ^ 2 / p.ε) + 1 + (p.σ0 * p.R / p.ε) ^ (p.α / (p.α - 1))) / p.δ⌉₊

theorem result : Convergence LongTails.Setups.AffineMomentConvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  rcases hO with ⟨g, ν, P, hIID, rfl, hc, hg, hlip, ⟨u, hu, hR⟩, ho⟩
  have hs : 0 ≤ p.σ := hp.2.2.1
  have hs0 : 0 ≤ p.σ0 := hp.2.2.2.1
  have hRad : 0 < p.R := hp.2.1
  have he : 0 < p.ε := hp.2.2.2.2.2.2.1
  have hd : 0 < p.δ := hp.2.2.2.2.2.2.2.1
  have hK : 0 < budget p 0 := by
    apply Nat.ceil_pos.mpr
    positivity
  exact LongTails.Proofs.StochasticEnvelopeRecursion.successful_execution p hp ν P hIID
    f g hc hg hlip u hu hR ho (budget p 0) hK (Nat.le_ceil _)

end LongTails.Theorems.RecursiveAffineMomentAcceleration
