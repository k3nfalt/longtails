import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Algorithms.BirchCollectionDelayed

namespace LongTails.Algorithms.BirchCollectionLocal

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)

structure Round (m : ℕ) where
  base : ℕ
  head : Fin m → ℕ
  pending : Fin m → Option Ticket := fun _ => none
  completed : ℕ := 0
  trace : TraceState
  events : List Event

def Round.initial (m : ℕ) (trace : TraceState) (events : List Event) : Round m :=
  let base := trace.markers.getLast?.getD 0
  { base, head := fun _ => base, trace, events }

def Round.append {m : ℕ} (s : Round m) (events : List Event) : Round m :=
  { s with trace := events.foldl step s.trace, events := s.events ++ events }

def localCapture {m : ℕ} (B : ℕ) (movement : ℝ) (s : Round m) (w : Fin m) : List Event :=
  .capture (w.val + 1) (s.head w) B 1 movement ::
    List.replicate B (.issue s.trace.nextCollection (w.val + 1))

def localComplete (B : ℕ) (t : Ticket) : List Event :=
  (List.range' t.firstRaw B).map Event.receive ++ [.finish t.collection]

def localAbort (B : ℕ) (t : Ticket) : List Event :=
  (List.range' t.firstRaw B).map Event.discard ++ [.cancel t.collection]

def Enabled {m : ℕ} (Q : ℕ) (s : Round m) : OriginalEvent m → Prop
  | .query w => s.completed < Q ∧ s.pending w = none
  | .reply w => s.completed < Q ∧ (s.pending w).isSome

def advance {m : ℕ} (B : ℕ) (movement : ℝ) (s : Round m) : OriginalEvent m → Round m
  | .query w =>
      { s.append (localCapture B movement s w) with
        pending := Function.update s.pending w (some ⟨s.trace.nextCollection, s.trace.nextRaw⟩) }
  | .reply w =>
      match s.pending w with
      | none => s
      | some t =>
        { s.append (localComplete B t) with
          head := Function.update s.head w s.trace.nextState
          pending := Function.update s.pending w none
          completed := s.completed + 1 }

def LegalFrom {m : ℕ} (Q B : ℕ) (movement : ℝ) : Round m → List (OriginalEvent m) → Prop
  | _, [] => True
  | s, e :: events => Enabled Q s e ∧ LegalFrom Q B movement (advance B movement s e) events

def abortPending {m : ℕ} (B : ℕ) (s : Round m) : Round m :=
  (List.finRange m).foldl (fun t w =>
    match t.pending w with
    | none => t
    | some j =>
      { t.append (localAbort B j) with pending := Function.update t.pending w none }) s

def joinHeads {m : ℕ} (s : Round m) : Round m :=
  let (out, head) := (List.finRange m).foldl (fun (t, left) w =>
    (t.append [.merge 0 left (s.head w) s.base], t.trace.nextState)) (s, s.base)
  out.append [.mark head]

def publish {m : ℕ} (B : ℕ) (s : Round m) : Round m :=
  joinHeads (abortPending B s)

def runRound {m : ℕ} (B : ℕ) (movement : ℝ) (s : Round m)
    (events : List (OriginalEvent m)) : Round m :=
  publish B (events.foldl (advance B movement) s)

def runRounds {m : ℕ} (B : ℕ) (movement : ℝ) (events : List (List (OriginalEvent m))) : Round m :=
  events.foldl (fun s es => runRound B movement (Round.initial m s.trace s.events) es)
    (Round.initial m {} [])

def CompleteRounds {m : ℕ} (Q B : ℕ) (movement : ℝ) :
    Round m → List (List (OriginalEvent m)) → Prop
  | _, [] => True
  | s, es :: rest =>
      let start := Round.initial m s.trace s.events
      let privateRound := es.foldl (advance B movement) start
      LegalFrom Q B movement start es ∧ privateRound.completed = Q ∧
        CompleteRounds Q B movement (publish B privateRound) rest

def localOrdering (Q K : ℕ) : LongTails.Setups.BirchCollections.Ordering where
  labels := List.range (K * Q)
  cut := fun k => k * Q
  frontier := fun n => (n / Q) * Q
  anchor := id
  scale := fun _ _ => 1
  renewalFrontier := fun _ _ => 0


open LongTails.Algorithms.BirchCollectionProfiles (controls divisor resetOrdering)

noncomputable def tuned (p : Params) (m Q : ℕ) : Params :=
  {p with workers := m + 1, controls := controls Q Q (Q - 1) 0}

noncomputable def localSgd (p : Params) (m Q : ℕ) (rounds : List (List (OriginalEvent m))) : Params :=
  let q := tuned p m Q
  let B := batchSize q
  let K := horizon q
  let move := 1 / (divisor Q (Q - 1) : ℝ)
  let s := runRounds B move rounds
  {q with
    controls := controls Q Q (Q - 1) (s.trace.nextRaw - B * (K * Q))
    events := s.events
    ordering := resetOrdering (localOrdering Q K)}

noncomputable abbrev Complete (p : Params) (m Q : ℕ) (rounds : List (List (OriginalEvent m))) : Prop :=
  let q := tuned p m Q
  rounds.length = horizon q ∧
    CompleteRounds Q (batchSize q) (1 / (divisor Q (Q - 1) : ℝ)) (Round.initial m {} []) rounds

end LongTails.Algorithms.BirchCollectionLocal
