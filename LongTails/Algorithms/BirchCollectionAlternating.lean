import LongTails.Algorithms.BirchCollectionNested
import LongTails.Algorithms.BirchCollectionBatches
import LongTails.Algorithms.BirchCollectionRetune

namespace LongTails.Algorithms.BirchCollectionAlternating

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested (Layout runRound)
open LongTails.Algorithms.BirchCollectionBatches (batchAndMarkWithMove)
open LongTails.Algorithms.BirchCollectionRetune (retune)

def cut (B k : ℕ) : ℕ := (k / 2) * (B + 1) + k % 2

noncomputable def gain (B : ℕ) (w : ℝ) : ℝ × ℝ :=
  if w = 1 / 2 then (1, 1 / 8)
  else if w = 1 / 4 then (1 / (8 * B), 1 / (8 * B))
  else (1, 1)

noncomputable def stepRound {m : ℕ} (layout : Layout m) (B : ℕ) (s : Round m)
    (k : ℕ) (order : List (Fin m)) : Round m :=
  if k % 2 = 0 then
    s.append (batchAndMarkWithMove s.trace 0 (s.trace.markers.getLast?.getD 0)
      (List.replicate B 0) (1 / 2))
  else runRound layout B 1 (1 / 4) s order

noncomputable def rounds {m : ℕ} (layout : Layout m) (B : ℕ)
    (orders : ℕ → List (Fin m)) : ℕ → Round m
  | 0 => Round.initial m {} []
  | k + 1 => stepRound layout B (rounds layout B orders k) k (orders k)

def anchor (B n : ℕ) : ℕ := (n / (B + 1)) * (B + 1)

def ordering (B K : ℕ) : LongTails.Setups.BirchCollections.Ordering where
  labels := List.range (cut B K)
  cut := cut B
  frontier := fun n => if n = anchor B n then n else anchor B n + 1
  anchor := anchor B
  scale := fun _ j => if j = 0 then 1 else 2
  renewalFrontier := fun _ j => if j = 0 then 0 else 1

noncomputable def controls (D : ℕ) : Controls where
  lowerMass := 1 / 8
  upperMass := 1 / 8
  massRatio := 1
  amplification := 8
  initialization := 0
  waste := D

noncomputable def alternating {m : ℕ} (p : Params) (layout : Layout m)
    (orders : ℕ → List (Fin m)) : Params :=
  let q := {p with workers := m + 1, controls := controls 0}
  let B := batchSize q
  let K := horizon q
  let s := rounds layout B orders K
  {q with
    controls := controls (s.trace.nextRaw - B * K)
    events := s.events.map (retune (gain B))
    ordering := ordering B K}

end LongTails.Algorithms.BirchCollectionAlternating
