import LongTails.Setups.AffineMomentConvex
import LongTails.Proofs.AffineMomentRun
import LongTails.Proofs.AffineMomentBudget

namespace LongTails.Theorems.AffineMomentAcceleration

open OracleTemplate LongTails.Setups.AffineMomentConvex
open LongTails.Algorithms.AffineMomentAccelerated

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ (256 * (p.α / (p.α - 1))) * ((1 + p.σ) ^ (p.α / (p.α - 1)) * (4 + p.L * p.R ^ 2 / p.ε) ^ (p.α / (3 * p.α - 2)) + (p.σ0 * (4 / (p.L * p.R) + p.R / p.ε)) ^ (p.α / (p.α - 1))) * (Real.log (20 + p.α / (p.α - 1) + p.L * p.R ^ 2 / p.ε + 1 / p.δ)) ^ (p.α / (p.α - 1) + 1)⌉₊

theorem result : Convergence LongTails.Setups.AffineMomentConvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  rcases hO with ⟨g, ν, P, hIID, rfl, hc, hg, hlip, ⟨u, hu, hR⟩, ho⟩
  exact LongTails.Proofs.AffineMomentRun.successful_execution p hp ν P hIID f g hc hg hlip u hu hR ho
    (budget p 0) (LongTails.Proofs.AffineMomentBudget.public_calls p hp)

end LongTails.Theorems.AffineMomentAcceleration
