import LongTails.Algorithms.BirchCollectionBatches
import LongTails.Algorithms.BirchNonEuclideanRennala

namespace LongTails.Algorithms.BirchCollectionRennala

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionBatches (vanillaOrdering vanillaControls)

abbrev OriginalEvent := LongTails.Algorithms.BirchNonEuclideanRennala.Event
abbrev OriginalState := LongTails.Algorithms.BirchNonEuclideanRennala.State

structure Translation (m : ℕ) where
  original : OriginalState m
  trace : TraceState
  active : ℕ
  raw : Fin m → ℕ
  events : List Event

def initial (m B : ℕ) : Translation m :=
  let e := Event.capture 0 0 B 1 1
  { original := {}
    trace := step {} e
    active := 0
    raw := fun _ => 0
    events := [e] }

def emissions {m : ℕ} (K B : ℕ) (s : Translation m) : OriginalEvent m → List Event
  | .query w =>
      if s.original.round < K ∧ s.original.source w = s.original.round then
        [.issue s.active (w.val + 1)]
      else
        [.capture 0 (s.original.source w) 1 1 0,
          .issue s.trace.nextCollection (w.val + 1), .cancel s.trace.nextCollection]
  | .reply w =>
      if s.original.round < K ∧ s.original.source w = s.original.round then
        if s.original.batch + 1 = B then
          [.receive (s.raw w), .finish s.active, .mark s.trace.nextState] ++
            if s.original.round + 1 < K then [.capture 0 s.trace.nextState B 1 1] else []
        else [.receive (s.raw w)]
      else [.discard (s.raw w)]

def advance {m : ℕ} (K B : ℕ) (s : Translation m) (e : OriginalEvent m) : Translation m :=
  let original := LongTails.Algorithms.BirchNonEuclideanRennala.step K B s.original e
  let issued := emissions K B s e
  { original
    trace := issued.foldl step s.trace
    active := if s.original.round < original.round ∧ original.round < K then
      s.trace.nextCollection else s.active
    raw := match e with
      | .query w => Function.update s.raw w s.trace.nextRaw
      | .reply _ => s.raw
    events := s.events ++ issued }

def translate {m : ℕ} (K B : ℕ) (events : List (OriginalEvent m)) : Translation m :=
  events.foldl (advance K B) (initial m B)

noncomputable def rennala (p : Params) (m : ℕ) (events : List (OriginalEvent m)) : Params :=
  let q := { p with workers := m + 1, controls := vanillaControls }
  let K := horizon q
  let B := batchSize q
  let translated := translate K B events
  { q with
    controls := { vanillaControls with
      waste := translated.original.stale.length + translated.original.drained.length }
    events := translated.events
    ordering := vanillaOrdering K }

end LongTails.Algorithms.BirchCollectionRennala
