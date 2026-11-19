import LongTails.Algorithms.DistributedLocalExtragradient

namespace LongTails.Algorithms.DistributedLocalExtragradientProcess

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

noncomputable def refineRun (p : Params) (s T : ℕ) (H : ℝ) (width : ℕ) (spacing r : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (center : Point p) (samples : ℕ → p.Ω) : ℕ → Point p
  | 0 => center
  | k + 1 => projectedBlockOutput p T (p.n * (s + 2 * T * k)) H width spacing center r g
      (refineRun p s T H width spacing r g center samples k) samples

end LongTails.Algorithms.DistributedLocalExtragradientProcess
