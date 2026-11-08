import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionWorkerPools

namespace LongTails.Algorithms.BirchCollectionCycle

open LongTails.Algorithms.BirchCollectionProfiles
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools

def upper (m s : ℕ) : ℕ := m * cycleGroups m s

def window (m s : ℕ) : ℕ := upper m s * cycleGroups m s - 1

noncomputable def tuned (p : Params) (m size : ℕ) : Params :=
  {p with workers := m + 1, controls := controls 1 (upper m size) (window m size) 0}

noncomputable def cycleSgd (p : Params) (m size : ℕ) : Params :=
  let q := tuned p m size
  let U := upper m size
  let W := window m size
  let B := batchSize q
  let s := cycle m size B (horizon q) (1 / (divisor U W : ℝ))
  {q with
    controls := controls 1 U W (s.trace.nextRaw - B * s.accepted.length)
    events := s.events
    ordering := resetOrdering (ordering s)}

end LongTails.Algorithms.BirchCollectionCycle
