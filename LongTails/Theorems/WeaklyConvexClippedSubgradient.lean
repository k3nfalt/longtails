import LongTails.Setups.WeaklyConvexHeavyTailed
import LongTails.Proofs.ClippedSubgradientConvergence

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * ⌈288 * q.ρ * q.Δ * (q.G ^ 2 + q.σ ^ q.α * (4 * q.G + 4 * q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1))) ^ (2 - q.α)) / q.ε ^ 4⌉₊

theorem result : Convergence LongTails.Setups.WeaklyConvexHeavyTailed.spec budget := by
  have h2 : ∀ q : Params, 2 * threshold q =
      4 * q.G + 4 * q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1)) := by
    intro q; unfold threshold; ring
  have hb : budget = fun q _ => 2 * steps q := by
    funext q i
    simp only [budget, steps, noiseScale, h2]
  rw [hb]
  exact convergence

end OracleTemplate.WeaklyConvexHeavyTailed
