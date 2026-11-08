import LongTails.Setups.BirchCollectionExecutionModel

namespace LongTails.Algorithms.BirchCollectionBatches

open LongTails.Setups.BirchCollections

def batchAndMarkWithMove (s : TraceState) (owner source : ℕ) (issuers : List ℕ)
    (move : ℝ) : List Event :=
  let capture := Event.capture owner source issuers.length 1 move
  capture :: (batchReplies s.nextCollection (step s capture) issuers ++
    [.finish s.nextCollection, .mark s.nextState])

abbrev batchAndMark (s : TraceState) (owner source : ℕ) (issuers : List ℕ) : List Event :=
  batchAndMarkWithMove s owner source issuers 1

def vanillaEvents (B : ℕ) : ℕ → List Event
  | 0 => []
  | k + 1 =>
      let events := vanillaEvents B k
      events ++ batchAndMark (run events) 0 k (List.replicate B 0)

def vanillaOrdering (K : ℕ) : LongTails.Setups.BirchCollections.Ordering where
  labels := List.range K
  cut := id
  frontier := id
  anchor := id
  scale := fun _ _ => 1
  renewalFrontier := fun _ _ => 0

def vanillaControls : Controls where
  lowerMass := 1
  upperMass := 1
  massRatio := 1
  amplification := 1
  initialization := 0
  waste := 0

noncomputable def vanilla (p : Params) : Params :=
  let q := { p with controls := vanillaControls }
  { q with events := vanillaEvents (batchSize q) (horizon q)
           ordering := vanillaOrdering (horizon q) }

end LongTails.Algorithms.BirchCollectionBatches
