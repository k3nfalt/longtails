import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionRennala
import LongTails.Algorithms.BirchCollectionBatches

namespace LongTails.Algorithms.BirchCollectionDelayed

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Algorithms.BirchCollectionBatches (vanillaOrdering)

structure SavedPoint where
  round : ℕ := 0
  point : ℕ := 0

structure Ticket where
  collection : ℕ
  firstRaw : ℕ

structure Controller (m : ℕ) where
  saved : Fin m → SavedPoint := fun _ => {}
  pending : Fin m → Option Ticket := fun _ => none
  trace : TraceState := {}
  events : List Event := []
  frontiers : List ℕ := []

def Controller.head {m : ℕ} (s : Controller m) : ℕ := s.trace.markers.getLast?.getD 0

def Controller.round {m : ℕ} (s : Controller m) : ℕ := s.trace.nextDirection

def Controller.append {m : ℕ} (s : Controller m) (events : List Event) : Controller m :=
  { s with trace := events.foldl step s.trace, events := s.events ++ events }

def accepts {m : ℕ} (K window : ℕ) (s : Controller m) (w : Fin m) : Prop :=
  s.round < K ∧ s.round - (s.saved w).round ≤ window

instance {m : ℕ} (K window : ℕ) (s : Controller m) (w : Fin m) :
    Decidable (accepts K window s w) := inferInstanceAs (Decidable (_ ∧ _))

def queryEvents {m : ℕ} (B : ℕ) (movement : ℝ) (s : Controller m) (w : Fin m) : List Event :=
  .capture (w.val + 1) (s.saved w).point B 1 movement ::
    List.replicate B (.issue s.trace.nextCollection (w.val + 1))

def replyEvents {m : ℕ} (K B window : ℕ) (s : Controller m) (w : Fin m) (t : Ticket) :
    List Event :=
  let raw := List.range' t.firstRaw B
  if accepts K window s w then
    raw.map Event.receive ++
      [.finish t.collection, .merge 0 s.head s.trace.nextState (s.saved w).point,
        .mark (s.trace.nextState + 1)]
  else
    raw.map Event.discard ++ [.cancel t.collection]

def Enabled {m : ℕ} (K : ℕ) (s : Controller m) : OriginalEvent m → Prop
  | .query w => s.round < K ∧ s.pending w = none
  | .reply w => (s.pending w).isSome

def advance {m : ℕ} (K B window : ℕ) (movement : ℝ) (s : Controller m) :
    OriginalEvent m → Controller m
  | .query w =>
      { s.append (queryEvents B movement s w) with
        pending := Function.update s.pending w
          (some ⟨s.trace.nextCollection, s.trace.nextRaw⟩) }
  | .reply w =>
      match s.pending w with
      | none => s
      | some t =>
        let out := s.append (replyEvents K B window s w t)
        { out with
          saved := Function.update s.saved w ⟨out.round, out.head⟩
          pending := Function.update s.pending w none
          frontiers := if accepts K window s w then s.frontiers ++ [(s.saved w).round] else s.frontiers }

def LegalFrom {m : ℕ} (K B window : ℕ) (movement : ℝ) :
    Controller m → List (OriginalEvent m) → Prop
  | _, [] => True
  | s, e :: events =>
      Enabled K s e ∧ LegalFrom K B window movement (advance K B window movement s e) events

def runController {m : ℕ} (K B window : ℕ) (movement : ℝ) (events : List (OriginalEvent m)) :
    Controller m := events.foldl (advance K B window movement) {}

def delayedOrdering (frontiers : List ℕ) : LongTails.Setups.BirchCollections.Ordering :=
  { vanillaOrdering frontiers.length with frontier := fun n => frontiers[n]?.getD 0 }


open LongTails.Algorithms.BirchCollectionProfiles (controls divisor resetOrdering)

noncomputable def tuned (p : Params) (m window : ℕ) : Params :=
  { p with workers := m + 1, controls := controls 1 1 window 0 }

noncomputable def delayed (p : Params) (m window : ℕ) (events : List (OriginalEvent m)) : Params :=
  let q := tuned p m window
  let B := batchSize q
  let K := horizon q
  let s := runController K B window (1 / (divisor 1 window : ℝ)) events
  { q with
    controls := controls 1 1 window (s.trace.nextRaw - B * K)
    events := s.events
    ordering := resetOrdering (delayedOrdering s.frontiers) }

noncomputable def ringmaster (p : Params) (m G : ℕ) (events : List (OriginalEvent m)) : Params :=
  delayed p m (G - 1) events

noncomputable abbrev Complete (p : Params) (m window : ℕ) (events : List (OriginalEvent m)) : Prop :=
  let q := tuned p m window
  let B := batchSize q
  let K := horizon q
  let movement := 1 / (divisor 1 window : ℝ)
  LegalFrom K B window movement {} events ∧ (runController K B window movement events).round = K

end LongTails.Algorithms.BirchCollectionDelayed
