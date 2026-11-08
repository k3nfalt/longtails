import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionWorkerPools

namespace LongTails.Algorithms.BirchCollectionMeta

open LongTails.Algorithms.BirchCollectionProfiles
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools

noncomputable def tuned (p : Params) (m Q : ℕ) : Params :=
  {p with workers := m + 1, controls := controls 1 Q (Q - 1) 0}

noncomputable def metaLocal (p : Params) (m Q : ℕ) (events : List (MetaEvent m)) : Params :=
  let q := tuned p m Q
  let B := batchSize q
  let s := metaRun Q B (1 / (divisor Q (Q - 1) : ℝ)) events
  {q with
    controls := controls 1 Q (Q - 1) (s.trace.nextRaw - B * s.accepted.length)
    events := s.events
    ordering := resetOrdering (ordering s)}

noncomputable abbrev Complete (p : Params) (m Q : ℕ) (events : List (MetaEvent m)) : Prop :=
  let q := tuned p m Q
  let B := batchSize q
  let move := 1 / (divisor Q (Q - 1) : ℝ)
  MetaLegal Q B move {} events ∧ (metaRun Q B move events).cuts.length = horizon q + 1

end LongTails.Algorithms.BirchCollectionMeta
