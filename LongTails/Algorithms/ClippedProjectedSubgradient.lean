import LongTails.Algorithms.Clipping
import LongTails.Setups.WeaklyConvexHeavyTailed
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

noncomputable def threshold (q : Params) : ℝ :=
  2 * q.G + 2 * q.σ * (4 * q.σ / q.ε) ^ (1 / (q.α - 1))

noncomputable def noiseScale (q : Params) : ℝ :=
  q.G ^ 2 + q.σ ^ q.α * (2 * threshold q) ^ (2 - q.α)

noncomputable def stepSize (q : Params) : ℝ := q.ε ^ 2 / (24 * q.ρ * noiseScale q)

noncomputable def steps (q : Params) : ℕ := ⌈288 * q.ρ * q.Δ * noiseScale q / q.ε ^ 4⌉₊

abbrev State (q : Params) := ClippedSubgradient.State q.E

noncomputable def algorithm (q : Params) : Algorithm (Query q) q.E q.E :=
  ClippedSubgradient.method (steps q) (stepSize q) (threshold q) q.x0

noncomputable def transition {Ω : Type*} (q : Params) (g : q.E → Ω → q.E)
    (projection : q.E → q.E) (x : q.E) (ω : Ω) : q.E :=
  projection (x - stepSize q • clip (threshold q) (g x ω))

noncomputable def trajectory {Ω : Type*} (q : Params) (g : q.E → Ω → q.E)
    (projection : q.E → q.E) (ξ : ℕ → Ω) : ℕ → q.E
  | 0 => q.x0
  | n + 1 => transition q g projection (trajectory q g projection ξ n) (ξ n)

end OracleTemplate.WeaklyConvexHeavyTailed
