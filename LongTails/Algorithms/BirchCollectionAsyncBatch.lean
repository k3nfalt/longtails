import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionDelayed

namespace LongTails.Algorithms.BirchCollectionAsyncBatch

open LongTails.Algorithms.BirchCollectionProfiles
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)

def delayWindow (G M : ℕ) : ℕ := (G - 1) / M

noncomputable def tuned (p : Params) (m G M : ℕ) : Params :=
  {p with workers := m + 1, controls := packetControls 1 1 (delayWindow G M) 0 M}

noncomputable def asyncBatch (p : Params) (m G M : ℕ) (events : List (OriginalEvent m)) : Params :=
  let q := tuned p m G M
  let W := delayWindow G M
  let B := batchSize q
  let K := horizon q
  let s := runController K (B * M) W (1 / (divisor 1 W : ℝ)) events
  { q with
    controls := packetControls 1 1 W (s.trace.nextRaw - B * M * K) M
    events := s.events
    ordering := resetOrdering (delayedOrdering s.frontiers) }

noncomputable abbrev Complete (p : Params) (m G M : ℕ) (events : List (OriginalEvent m)) : Prop :=
  let q := tuned p m G M
  let B := batchSize q
  let K := horizon q
  let W := delayWindow G M
  let movement := 1 / (divisor 1 W : ℝ)
  LegalFrom K (B * M) W movement {} events ∧ (runController K (B * M) W movement events).round = K

end LongTails.Algorithms.BirchCollectionAsyncBatch
