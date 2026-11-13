import LongTails.Setups.BirchAveragingDiscovery
import LongTails.Algorithms.BirchAveraging

namespace OracleTemplate.BirchAveragingDiscovery

open OracleTemplate
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID
open LongTails.Setups.BirchAveragingDiscovery

def horizon {workers : ℕ} (p : Parameters workers) : ℕ := max 1 p.localSteps

noncomputable def rounds {workers : ℕ} (p : Parameters workers) : ℕ :=
  max 1 ⌈if p.base.δ = 0 then 8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε)
    else max (8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε))
      (16 * p.base.L * p.base.Δ / (p.base.ε * Real.log (1 + p.base.L / p.base.δ)))⌉₊

noncomputable def step {workers : ℕ} (p : Parameters workers) : ℝ :=
  if p.base.δ = 0 then 1 / (4 * p.base.L) else logarithmicStep p.base.L p.base.δ (horizon p)

/-- The witness is the actual corrected endpoint-averaging method. -/
noncomputable def makeAlgorithm (n : ℕ) (p : Parameters (n + 1)) :
    Algorithm (Point p.base.d) (Point p.base.d) (Point p.base.d) (n + 1) :=
  correctedAveraging (n + 1) p.base.d (horizon p) (rounds p) (Nat.succ_pos n)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) p.base.x0 (step p)

end OracleTemplate.BirchAveragingDiscovery
